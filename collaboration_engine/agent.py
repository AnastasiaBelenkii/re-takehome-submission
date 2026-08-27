"""Two-model H+D engine with collaboration isolated behind peer packets."""

from __future__ import annotations

import asyncio
import os
from dataclasses import asdict, dataclass, field
from typing import Any

from baselines.simple_agent import _extract_lean
from re_harness import AgentResult, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded

from .constants import DESIGN_ID, MODELS
from .strategies import (
    CollaborationStrategy,
    PeerPacket,
    TrackObservation,
    create_strategy,
)
from uplift_pilot.agent import (
    _bounded_excerpt,
    _diagnostics,
    _normalized_candidate,
    _sha256,
)


@dataclass
class AttemptRecord:
    attempt: int
    call: int
    round: int
    phase: str
    candidate_sha256: str
    error_signature_sha256: str
    accepted: bool
    timed_out: bool
    raw_diagnostic_count: int
    diagnostic_excerpt: str
    checkpoint_saved: bool
    peer_packet_used: bool
    restart_reason: str | None = None


@dataclass
class TrackState:
    model: str
    candidate: str
    calls: int = 0
    feedback: str = ""
    restarts: int = 0
    restart_pending: bool = False
    failure_memory: list[str] = field(default_factory=list)
    seen_candidates: set[str] = field(default_factory=set)
    signature_run: int = 0
    previous_signature: str | None = None
    attempts: list[AttemptRecord] = field(default_factory=list)
    call_errors: list[dict[str, Any]] = field(default_factory=list)
    pending_packet: PeerPacket | None = None
    active: bool = True


class CollaborationEngineAgent:
    """Own every solve-loop decision except bounded peer information sharing."""

    def __init__(
        self,
        *,
        strategy: CollaborationStrategy,
        condition: str = "test",
        max_calls_per_model: int = 25,
        generation_max_tokens: int = 12000,
        temperature: float = 0.2,
        max_restarts: int = 2,
        diagnostic_chars: int = 6000,
        failure_memory_chars: int = 3000,
        peer_packet_chars: int = 6000,
    ) -> None:
        if not 1 <= max_calls_per_model <= 25:
            raise ValueError("max_calls_per_model must be between 1 and 25")
        if not 1 <= max_restarts <= 2:
            raise ValueError("max_restarts must be between 1 and 2")
        if not 1 <= peer_packet_chars <= 12000:
            raise ValueError("peer_packet_chars must be between 1 and 12000")
        self.strategy = strategy
        self.condition = condition
        self.max_calls_per_model = max_calls_per_model
        self.generation_max_tokens = generation_max_tokens
        self.temperature = temperature
        self.max_restarts = max_restarts
        self.diagnostic_chars = diagnostic_chars
        self.failure_memory_chars = failure_memory_chars
        self.peer_packet_chars = peer_packet_chars

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        tracks = {model: TrackState(model=model, candidate=problem.challenge) for model in MODELS}
        best_candidate = problem.challenge
        best_model: str | None = None
        best_rank: tuple[int, int, int] | None = None
        packet_events: list[dict[str, Any]] = []
        round_number = 0

        while any(track.active and track.calls < self.max_calls_per_model for track in tracks.values()):
            round_number += 1
            scheduled = [
                tracks[model]
                for model in MODELS
                if tracks[model].active and tracks[model].calls < self.max_calls_per_model
            ]
            requests = []
            phases: dict[str, str] = {}
            used_packets: dict[str, PeerPacket | None] = {}
            for track in scheduled:
                phase = "direct" if not track.attempts else ("restart" if track.restart_pending else "repair")
                phases[track.model] = phase
                used_packets[track.model] = track.pending_packet
                track.pending_packet = None
                track.calls += 1
                requests.append(self._call(track, problem, phase, used_packets[track.model], services))

            responses = await asyncio.gather(*requests, return_exceptions=True)
            observations: list[TrackObservation] = []
            accepted = False
            for track, response in zip(scheduled, responses, strict=True):
                phase = phases[track.model]
                packet = used_packets[track.model]
                if isinstance(response, (BudgetAccountingError, BudgetExceeded)):
                    track.calls -= 1
                    track.active = False
                    track.call_errors.append(self._error(response, track.calls + 1, phase, False))
                    continue
                if isinstance(response, BaseException):
                    track.call_errors.append(self._error(response, track.calls, phase, True))
                    track.restart_pending = False
                    continue

                track.candidate = _extract_lean(response.content, fallback=track.candidate)
                normalized = _normalized_candidate(track.candidate)
                candidate_hash = _sha256(normalized)
                repeated = candidate_hash in track.seen_candidates
                track.seen_candidates.add(candidate_hash)
                check = await services.lean.check_file(track.candidate)
                diagnostic_text, signature, raw_count = _diagnostics(
                    check.messages, limit=self.diagnostic_chars
                )
                rank = (0 if check.accepted else 1, 1 if check.timed_out else 0, raw_count)
                checkpoint_saved = best_rank is None or rank < best_rank
                if checkpoint_saved:
                    best_rank = rank
                    best_candidate = track.candidate
                    best_model = track.model
                    services.checkpoint(best_candidate, self._checkpoint_metadata(track, round_number, candidate_hash))

                record = AttemptRecord(
                    attempt=len(track.attempts) + 1,
                    call=track.calls,
                    round=round_number,
                    phase=phase,
                    candidate_sha256=candidate_hash,
                    error_signature_sha256=signature,
                    accepted=bool(check.accepted),
                    timed_out=bool(check.timed_out),
                    raw_diagnostic_count=raw_count,
                    diagnostic_excerpt=diagnostic_text,
                    checkpoint_saved=checkpoint_saved,
                    peer_packet_used=packet is not None,
                )
                track.attempts.append(record)
                track.restart_pending = False
                observations.append(TrackObservation(
                    model=track.model, round=round_number, call=track.calls,
                    candidate=track.candidate, diagnostics=diagnostic_text,
                    accepted=bool(check.accepted), timed_out=bool(check.timed_out),
                ))
                if check.accepted:
                    accepted = True
                    break

                track.feedback = diagnostic_text or (
                    "Lean timed out while checking the candidate."
                    if check.timed_out
                    else "Lean rejected the candidate without a diagnostic message."
                )
                self._update_decomposition(
                    track, signature, repeated, problem.challenge
                )

            if accepted:
                break
            packets = tuple(self.strategy.after_round(tuple(observations)))
            self._install_packets(packets, tracks, round_number, packet_events)

        metadata = {
            "design_id": DESIGN_ID,
            "condition": self.condition,
            "uplift_policy": "H+D",
            "collaboration_strategy": self.strategy.strategy_id,
            "selected_model": best_model,
            "selection_reason": "accepted" if best_rank and best_rank[0] == 0 else "global_best_checkpoint",
            "max_calls_per_model": self.max_calls_per_model,
            "max_total_calls": self.max_calls_per_model * len(MODELS),
            "calls_dispatched": sum(track.calls for track in tracks.values()),
            "packet_events": packet_events,
            "tracks": {
                model: {
                    "calls_dispatched": track.calls,
                    "restarts": track.restarts,
                    "attempts": [asdict(attempt) for attempt in track.attempts],
                    "call_errors": track.call_errors,
                    "failure_memory_entries": len(track.failure_memory),
                }
                for model, track in tracks.items()
            },
        }
        return AgentResult(best_candidate, metadata)

    async def _call(self, track: TrackState, problem: Problem, phase: str, packet: PeerPacket | None, services: Services):
        return await services.llm.complete(
            model=track.model,
            messages=self._messages(problem, track, phase, packet),
            max_tokens=self.generation_max_tokens,
            temperature=self.temperature,
        )

    def _messages(self, problem: Problem, track: TrackState, phase: str, packet: PeerPacket | None) -> list[dict[str, str]]:
        system = [
            "Write one complete Lean 4 file using Mathlib.",
            "Return only Lean code, preferably in one ```lean block.",
            "Preserve all theorem names and statements from the pristine challenge.",
            "Do not use sorry, admit, axioms, or unsafe escapes.",
        ]
        if phase == "restart":
            system.append("Abandon the prior trajectory and use a materially different mathematical or Lean strategy.")
        user = [
            f"Problem id: {problem.id}",
            f"Attempt {track.calls} of at most {self.max_calls_per_model}; phase: {phase}",
            "", "Problem description:", problem.description,
            "", "Pristine Lean challenge:", "```lean", problem.challenge, "```",
        ]
        if phase == "repair":
            user.extend(["", "Current candidate to repair:", "```lean", track.candidate, "```"])
        if track.feedback:
            user.extend(["", "Bounded deduplicated Lean diagnostics:", "```text", track.feedback, "```"])
        if track.failure_memory:
            user.extend(["", "Bounded failed-approach memory (do not repeat these strategies):", "```text", "\n".join(track.failure_memory), "```"])
        if packet is not None:
            user.extend(["", "Evidence from an independent solver. Critically evaluate it; reuse only what helps:", "```text", packet.content, "```"])
        return [{"role": "system", "content": "\n".join(system)}, {"role": "user", "content": "\n".join(user)}]

    def _update_decomposition(
        self,
        track: TrackState,
        signature: str,
        repeated: bool,
        pristine_challenge: str,
    ) -> None:
        track.signature_run = track.signature_run + 1 if signature == track.previous_signature else 1
        track.previous_signature = signature
        reason = "repeated_normalized_candidate" if repeated else (
            "unchanged_error_signature_two_transitions" if track.signature_run >= 3 else None
        )
        if reason and track.restarts < self.max_restarts:
            track.restarts += 1
            track.attempts[-1].restart_reason = reason
            # Hashes remain in the machine-readable ledger, never model-visible.
            memory_limit = max(1, self.failure_memory_chars // self.max_restarts)
            labels = "Failed Lean candidate excerpt:\n\nLean diagnostics:\n"
            available = max(0, memory_limit - len(labels))
            candidate_limit = max(1, (available * 2) // 3)
            feedback_limit = max(1, available - candidate_limit)
            track.failure_memory.append(
                "\n".join(
                    [
                        "Failed Lean candidate excerpt:",
                        _bounded_excerpt(track.candidate, limit=candidate_limit),
                        "Lean diagnostics:",
                        _bounded_excerpt(track.feedback, limit=feedback_limit),
                    ]
                )[:memory_limit]
            )
            while len("\n".join(track.failure_memory)) > self.failure_memory_chars and len(track.failure_memory) > 1:
                track.failure_memory.pop(0)
            track.candidate = pristine_challenge
            track.feedback = ""
            track.previous_signature = None
            track.signature_run = 0
            track.restart_pending = True

    def _install_packets(self, packets: tuple[PeerPacket, ...], tracks: dict[str, TrackState], round_number: int, events: list[dict[str, Any]]) -> None:
        targets: set[str] = set()
        for packet in packets:
            if packet.target_model not in tracks or packet.source_model not in tracks:
                raise ValueError("strategy returned a packet for an unknown model")
            if packet.target_model == packet.source_model:
                raise ValueError("strategy packets must be cross-model")
            if packet.target_model in targets:
                raise ValueError("strategy returned multiple packets for one target")
            if len(packet.content) > self.peer_packet_chars:
                raise ValueError("strategy packet exceeds peer_packet_chars")
            if not packet.content.strip():
                raise ValueError("strategy packet must not be empty")
            targets.add(packet.target_model)
            tracks[packet.target_model].pending_packet = packet
            events.append({
                "after_round": round_number, "target_model": packet.target_model,
                "source_model": packet.source_model, "kind": packet.kind,
                "content_chars": len(packet.content), "content_sha256": _sha256(packet.content),
            })

    def _checkpoint_metadata(self, track: TrackState, round_number: int, candidate_hash: str) -> dict[str, Any]:
        return {
            "design_id": DESIGN_ID, "condition": self.condition,
            "uplift_policy": "H+D", "collaboration_strategy": self.strategy.strategy_id,
            "model": track.model, "call": track.calls, "round": round_number,
            "candidate_sha256": candidate_hash,
        }

    @staticmethod
    def _error(exc: BaseException, call: int, phase: str, dispatched: bool) -> dict[str, Any]:
        return {"call": call, "phase": phase, "dispatched": dispatched, "type": type(exc).__name__, "message": str(exc)[:1000]}


def _env_int(name: str, default: int, minimum: int, maximum: int) -> int:
    try:
        value = int(os.environ.get(name, str(default)))
    except ValueError as exc:
        raise ValueError(f"{name} must be an integer") from exc
    if not minimum <= value <= maximum:
        raise ValueError(f"{name} must be between {minimum} and {maximum}")
    return value


def create_agent() -> CollaborationEngineAgent:
    if os.environ.get("COLLAB_DESIGN_ID", DESIGN_ID) != DESIGN_ID:
        raise ValueError(f"COLLAB_DESIGN_ID must be {DESIGN_ID}")
    condition = os.environ.get("COLLAB_CONDITION", "").strip()
    strategy_id = os.environ.get("COLLAB_STRATEGY", "").strip()
    if not condition or not strategy_id:
        raise ValueError("COLLAB_CONDITION and COLLAB_STRATEGY are required")
    packet_chars = _env_int("COLLAB_PEER_PACKET_CHARS", 6000, 1, 12000)
    return CollaborationEngineAgent(
        strategy=create_strategy(strategy_id, packet_chars=packet_chars),
        condition=condition,
        max_calls_per_model=_env_int("COLLAB_MAX_CALLS_PER_MODEL", 25, 1, 25),
        generation_max_tokens=_env_int("COLLAB_GENERATION_MAX_TOKENS", 12000, 1000, 32000),
        max_restarts=_env_int("COLLAB_MAX_RESTARTS", 2, 1, 2),
        diagnostic_chars=_env_int("COLLAB_DIAGNOSTIC_CHARS", 6000, 500, 12000),
        failure_memory_chars=_env_int("COLLAB_FAILURE_MEMORY_CHARS", 3000, 500, 6000),
        peer_packet_chars=packet_chars,
        temperature=float(os.environ.get("COLLAB_TEMPERATURE", "0.2")),
    )
