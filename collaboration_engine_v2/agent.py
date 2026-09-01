"""Frozen two-model base with C0/C1/C2 packet-only treatments."""

from __future__ import annotations

import asyncio
import os
import time
from dataclasses import asdict, dataclass, field
from typing import Any, Callable

from baselines.simple_agent import _extract_lean
from re_harness import AgentResult, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.llm import CostFreeRateLimitError
from uplift_pilot.agent import _bounded_excerpt, _diagnostics, _normalized_candidate, _sha256

from .constants import DESIGN_ID, MODELS
from .strategies import CollaborationStrategy, PeerPacket, TrackObservation, create_strategy
from .tactics import (
    canonicalize_imports,
    imports_unchanged,
    required_declarations_present,
    tactic_candidate,
)


@dataclass
class AttemptRecord:
    attempt: int
    call: int
    round: int
    phase: str
    candidate_sha256: str
    error_signature_sha256: str
    lean_accepted: bool
    accepted: bool
    compatibility_checked: bool
    compatibility_passed: bool
    timed_out: bool
    raw_diagnostic_count: int
    diagnostic_excerpt: str
    checkpoint_saved: bool
    peer_packet_used: bool
    required_declarations_present: bool
    original_imports_unchanged: bool
    imports_normalized: bool
    proposal_committed: bool
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
    retry_events: list[dict[str, Any]] = field(default_factory=list)
    pending_packets: list[tuple[PeerPacket, dict[str, Any]]] = field(default_factory=list)
    active: bool = True


class CollaborationEngineV2Agent:
    def __init__(
        self, *, strategy: CollaborationStrategy, condition: str = "test",
        max_calls_per_model: int | None = 25, generation_max_tokens: int = 12000,
        temperature: float = 0.2, seed: int = 1, max_restarts: int = 2,
        diagnostic_chars: int = 6000, failure_memory_chars: int = 3000,
        peer_packet_chars: int = 6000, dispatch_cutoff_s: float = 960,
        max_cost_free_429_retries: int = 2, retry_backoff_s: float = 1.0,
        clock: Callable[[], float] = time.monotonic,
    ) -> None:
        if max_calls_per_model is not None and not 1 <= max_calls_per_model <= 25:
            raise ValueError("max_calls_per_model must be 1..25 or None")
        if not 1 <= max_restarts <= 2:
            raise ValueError("max_restarts must be between 1 and 2")
        if not 0 <= max_cost_free_429_retries <= 5:
            raise ValueError("max_cost_free_429_retries must be between 0 and 5")
        if dispatch_cutoff_s <= 0:
            raise ValueError("dispatch_cutoff_s must be positive")
        self.strategy = strategy
        self.condition = condition
        self.max_calls_per_model = max_calls_per_model
        self.generation_max_tokens = generation_max_tokens
        self.temperature = temperature
        self.seed = seed
        self.max_restarts = max_restarts
        self.diagnostic_chars = diagnostic_chars
        self.failure_memory_chars = failure_memory_chars
        self.peer_packet_chars = peer_packet_chars
        self.dispatch_cutoff_s = dispatch_cutoff_s
        self.max_cost_free_429_retries = max_cost_free_429_retries
        self.retry_backoff_s = retry_backoff_s
        self.clock = clock

    def _has_capacity(self, track: TrackState) -> bool:
        return track.active and (
            self.max_calls_per_model is None or track.calls < self.max_calls_per_model
        )

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        started = self.clock()
        tracks = {model: TrackState(model=model, candidate=problem.challenge) for model in MODELS}
        best_candidate = problem.challenge
        best_model: str | None = None
        best_rank: tuple[int, int, int] | None = None
        packet_events: list[dict[str, Any]] = []
        deterministic: dict[str, Any] = {
            "attempted": False,
            "lean_accepted": False,
            "compatibility_checked": False,
            "accepted": False,
        }

        call_zero = tactic_candidate(problem.challenge)
        if call_zero is not None:
            call_zero = canonicalize_imports(call_zero)
            deterministic["attempted"] = True
            deterministic["candidate_sha256"] = _sha256(_normalized_candidate(call_zero))
            check = await services.lean.check_file(call_zero)
            verification = await self._verify_if_promising(call_zero, check.accepted, services)
            accepted = bool(check.accepted and verification.get("passed"))
            deterministic.update({
                "lean_accepted": bool(check.accepted),
                "compatibility_checked": bool(check.accepted),
                "compatibility": verification,
                "accepted": accepted, "timed_out": bool(check.timed_out),
                "raw_diagnostic_count": len(check.messages),
            })
            if not check.accepted:
                rank = (1, 1 if check.timed_out else 0, len(check.messages))
                best_candidate, best_rank = call_zero, rank
                services.checkpoint(call_zero, {
                    "design_id": DESIGN_ID, "condition": self.condition,
                    "phase": "deterministic_call_zero",
                    "candidate_sha256": deterministic["candidate_sha256"],
                    "compatibility_status": "provisional_lean_failure",
                })
            if accepted:
                best_candidate, best_rank = call_zero, (0, 0, 0)
                services.checkpoint(call_zero, {
                    "design_id": DESIGN_ID, "condition": self.condition,
                    "phase": "deterministic_call_zero",
                    "candidate_sha256": deterministic["candidate_sha256"],
                    "compatibility_status": "fresh_comparator_passed",
                })
                return AgentResult(call_zero, self._metadata(
                    tracks, packet_events, deterministic, best_model=None,
                    best_rank=best_rank, rounds=0, cutoff_reached=False,
                    provider_requests=self._provider_requests(services),
                ))

        cutoff_reached = False
        observations_by_round: dict[int, dict[str, TrackObservation]] = {}
        pending: dict[
            asyncio.Task,
            tuple[TrackState, str, PeerPacket | None, dict[str, Any] | None, int],
        ] = {}
        owner_task = asyncio.current_task()

        def cancel_children_if_owner_cancelled(task: asyncio.Task) -> None:
            if task.cancelled():
                for child in tuple(pending):
                    child.cancel()

        if owner_task is not None:
            owner_task.add_done_callback(cancel_children_if_owner_cancelled)

        def schedule(track: TrackState, *, check_cutoff: bool = True) -> bool:
            nonlocal cutoff_reached
            if not self._has_capacity(track):
                return False
            if check_cutoff and self.clock() - started >= self.dispatch_cutoff_s:
                cutoff_reached = True
                return False
            phase = "direct" if not track.attempts else (
                "restart" if track.restart_pending else "repair"
            )
            packet: PeerPacket | None = None
            packet_event: dict[str, Any] | None = None
            if track.pending_packets:
                packet, packet_event = track.pending_packets.pop(0)
            track.calls += 1
            call_round = track.calls
            if packet_event is not None:
                packet_event["used_on_call"] = track.calls
                packet_event["used_on_round"] = call_round
            task = asyncio.create_task(
                self._call(track, problem, phase, packet, services)
            )
            pending[task] = (track, phase, packet, packet_event, call_round)
            return True

        if self.clock() - started >= self.dispatch_cutoff_s:
            cutoff_reached = True
        else:
            for model in MODELS:
                schedule(tracks[model], check_cutoff=False)

        verified_success = False
        while pending:
            completed, _still_pending = await asyncio.wait(
                tuple(pending), return_when=asyncio.FIRST_COMPLETED
            )
            ready_to_schedule: list[TrackState] = []
            completed_observation_rounds: set[int] = set()
            ordered_completed = sorted(
                completed,
                key=lambda task: MODELS.index(pending[task][0].model),
            )
            for task in ordered_completed:
                track, phase, packet, _packet_event, call_round = pending.pop(task)
                try:
                    response = task.result()
                except BaseException as exc:
                    response = exc
                if isinstance(response, (BudgetAccountingError, BudgetExceeded)):
                    track.calls -= 1
                    track.active = False
                    track.call_errors.append(self._error(response, track.calls + 1, phase, False))
                    continue
                if isinstance(response, BaseException):
                    track.call_errors.append(self._error(response, track.calls, phase, True))
                    track.restart_pending = False
                    ready_to_schedule.append(track)
                    continue

                extracted = _extract_lean(response.content, fallback=track.candidate)
                original_imports_ok = imports_unchanged(problem.challenge, extracted)
                proposal = canonicalize_imports(extracted)
                declarations_ok = required_declarations_present(problem.challenge, proposal)
                imports_normalized = proposal != extracted
                contract_ok = declarations_ok
                compatibility: dict[str, Any] = {}
                lean_accepted = False
                if contract_ok:
                    check = await services.lean.check_file(proposal)
                    diagnostic_text, signature, raw_count = _diagnostics(check.messages, limit=self.diagnostic_chars)
                    lean_accepted, timed_out = bool(check.accepted), bool(check.timed_out)
                    compatibility = await self._verify_if_promising(
                        proposal, lean_accepted, services
                    )
                    accepted = bool(lean_accepted and compatibility.get("passed"))
                    if lean_accepted and not accepted:
                        diagnostic_text = self._compatibility_diagnostic(compatibility)
                        signature, raw_count = _sha256(diagnostic_text), 1
                    track.candidate = proposal
                else:
                    violations = []
                    if not declarations_ok:
                        violations.append(
                            "missing, duplicated, or incompatibly declared a required name"
                        )
                    diagnostic_text = (
                        "Candidate contract rejected before Lean: " + " and ".join(violations)
                        + ". Return a complete file containing every required declaration once; "
                          "additional helper declarations are allowed. Imports are normalized by "
                          "the harness."
                    )
                    signature, raw_count = _sha256(diagnostic_text), 1
                    accepted = lean_accepted = timed_out = False
                normalized = _normalized_candidate(proposal)
                candidate_hash = _sha256(normalized)
                repeated = candidate_hash in track.seen_candidates
                track.seen_candidates.add(candidate_hash)
                rank = (
                    0 if accepted else (1 if contract_ok else 2),
                    1 if timed_out else 0,
                    raw_count,
                )
                checkpoint_saved = (
                    contract_ok and not lean_accepted
                    and (best_rank is None or rank < best_rank)
                ) or accepted
                if checkpoint_saved:
                    best_rank, best_candidate, best_model = rank, proposal, track.model
                    checkpoint_metadata = self._checkpoint_metadata(
                        track, call_round, candidate_hash
                    )
                    checkpoint_metadata["compatibility_status"] = (
                        "fresh_comparator_passed" if accepted
                        else "provisional_lean_failure"
                    )
                    services.checkpoint(best_candidate, checkpoint_metadata)
                record = AttemptRecord(
                    len(track.attempts) + 1, track.calls, call_round, phase,
                    candidate_hash, signature, lean_accepted, accepted,
                    lean_accepted, bool(compatibility.get("passed")),
                    timed_out, raw_count,
                    diagnostic_text, checkpoint_saved, packet is not None,
                    declarations_ok, original_imports_ok, imports_normalized, contract_ok,
                )
                track.attempts.append(record)
                track.restart_pending = False
                observation = TrackObservation(
                    track.model, call_round, track.calls, track.candidate,
                    diagnostic_text, accepted, timed_out,
                )
                observations_by_round.setdefault(call_round, {})[track.model] = observation
                completed_observation_rounds.add(call_round)
                verified_success = verified_success or accepted
                if not accepted:
                    track.feedback = diagnostic_text or (
                        "Lean timed out while checking the candidate." if timed_out
                        else "Lean rejected the candidate without a diagnostic message."
                    )
                    self._update_decomposition(track, signature, repeated, problem.challenge)
                    ready_to_schedule.append(track)

            for completed_round in sorted(completed_observation_rounds):
                paired = observations_by_round.get(completed_round, {})
                if len(paired) != len(MODELS):
                    continue
                observations = tuple(paired[model] for model in MODELS)
                packets = tuple(self.strategy.after_round(observations))
                self._install_packets(packets, tracks, completed_round, packet_events)
                del observations_by_round[completed_round]

            if verified_success:
                if pending:
                    await asyncio.gather(*tuple(pending), return_exceptions=True)
                    pending.clear()
                break

            if ready_to_schedule:
                if self.clock() - started >= self.dispatch_cutoff_s:
                    cutoff_reached = True
                else:
                    for track in ready_to_schedule:
                        schedule(track, check_cutoff=False)

        round_number = max((track.calls for track in tracks.values()), default=0)

        if owner_task is not None:
            owner_task.remove_done_callback(cancel_children_if_owner_cancelled)

        return AgentResult(best_candidate, self._metadata(
            tracks, packet_events, deterministic, best_model=best_model,
            best_rank=best_rank, rounds=round_number, cutoff_reached=cutoff_reached,
            provider_requests=self._provider_requests(services),
        ))

    @staticmethod
    def _provider_requests(services: Services) -> dict[str, int]:
        raw = getattr(services.llm, "requests_dispatched_by_model", {})
        return {model: int(raw.get(model, 0)) for model in MODELS}

    async def _verify_if_promising(
        self, proposal: str, lean_accepted: bool, services: Services
    ) -> dict[str, Any]:
        if not lean_accepted:
            return {}
        try:
            result = dict(await services.verify(proposal))
        except asyncio.CancelledError:
            raise
        except Exception as exc:
            return {
                "passed": False,
                "verification_error": f"{type(exc).__name__}: {exc}"[:1000],
            }
        result["passed"] = bool(result.get("passed"))
        return result

    @staticmethod
    def _compatibility_diagnostic(verification: dict[str, Any]) -> str:
        if verification.get("verification_error"):
            detail = verification["verification_error"]
        else:
            detail = (
                f"answer_shape_passed={verification.get('answer_shape_passed')}; "
                f"comparator_passed={verification.get('comparator_passed')}; "
                f"comparator_timed_out={verification.get('comparator_timed_out')}; "
                f"comparator_exit_code={verification.get('comparator_exit_code')}"
            )
        return (
            "Warm Lean accepted this proposal, but fresh holdout-style verification "
            f"did not: {detail}. Continue from it only as an untrusted local repair "
            "state; it cannot stop the run or become a trusted checkpoint."
        )

    async def _call(self, track: TrackState, problem: Problem, phase: str,
                    packet: PeerPacket | None, services: Services):
        messages = self._messages(problem, track, phase, packet)
        for physical_attempt in range(1, self.max_cost_free_429_retries + 2):
            try:
                return await services.llm.complete(
                    model=track.model, messages=messages,
                    max_tokens=self.generation_max_tokens, temperature=self.temperature,
                    seed=self.seed,
                    reasoning={"effort": "medium"},
                )
            except CostFreeRateLimitError as exc:
                track.retry_events.append({
                    "semantic_call": track.calls, "physical_attempt": physical_attempt,
                    "cost_status": exc.cost_status, "status_code": exc.status_code,
                })
                if physical_attempt > self.max_cost_free_429_retries:
                    raise
                if self.retry_backoff_s:
                    await asyncio.sleep(self.retry_backoff_s * physical_attempt)

    def _messages(self, problem: Problem, track: TrackState, phase: str,
                  packet: PeerPacket | None) -> list[dict[str, str]]:
        system = [
            "Write one complete Lean 4 file using Mathlib.",
            "Return only Lean code, preferably in one ```lean block.",
            "Use exactly one import line: `import Mathlib`.",
            "Preserve every declaration name, type/statement, and numeric answer from the pristine challenge.",
            "You may add new helper lemmas or definitions with fresh names.",
            "Do not use sorry, admit, axioms, or unsafe escapes.",
        ]
        if phase in {"direct", "restart"}:
            system.append("Immediately before each new proof, include a 3-8 line proof sketch using Lean line comments (`--`).")
        if phase == "restart":
            system.append("Abandon the prior trajectory and use a materially different mathematical or Lean strategy.")
        maximum = str(self.max_calls_per_model) if self.max_calls_per_model is not None else "the external time/budget limit"
        user = [
            f"Problem id: {problem.id}", f"Attempt {track.calls} of at most {maximum}; phase: {phase}",
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

    def _update_decomposition(self, track: TrackState, signature: str, repeated: bool,
                              pristine_challenge: str) -> None:
        track.signature_run = track.signature_run + 1 if signature == track.previous_signature else 1
        track.previous_signature = signature
        reason = "repeated_normalized_candidate" if repeated else (
            "unchanged_error_signature_two_transitions" if track.signature_run >= 3 else None
        )
        if reason and track.restarts < self.max_restarts:
            track.restarts += 1
            track.attempts[-1].restart_reason = reason
            memory_limit = max(1, self.failure_memory_chars // self.max_restarts)
            candidate_limit = max(1, (memory_limit * 2) // 3)
            track.failure_memory.append((
                "Failed Lean candidate excerpt:\n" + _bounded_excerpt(track.candidate, limit=candidate_limit)
                + "\nLean diagnostics:\n" + _bounded_excerpt(track.feedback, limit=max(1, memory_limit-candidate_limit-50))
            )[:memory_limit])
            while len("\n".join(track.failure_memory)) > self.failure_memory_chars and len(track.failure_memory) > 1:
                track.failure_memory.pop(0)
            track.candidate, track.feedback = pristine_challenge, ""
            track.previous_signature, track.signature_run = None, 0
            track.restart_pending = True

    def _install_packets(self, packets: tuple[PeerPacket, ...], tracks: dict[str, TrackState],
                         round_number: int, events: list[dict[str, Any]]) -> None:
        targets: set[str] = set()
        for packet in packets:
            if packet.target_model not in tracks or packet.source_model not in tracks:
                raise ValueError("strategy returned a packet for an unknown model")
            if packet.target_model == packet.source_model or packet.target_model in targets:
                raise ValueError("strategy packets must be one cross-model packet per target")
            if not packet.content.strip() or len(packet.content) > self.peer_packet_chars:
                raise ValueError("strategy packet is empty or oversized")
            targets.add(packet.target_model)
            event = {
                "after_round": round_number, "target_model": packet.target_model,
                "source_model": packet.source_model, "kind": packet.kind,
                "content_chars": len(packet.content), "content_sha256": _sha256(packet.content),
                "queue_position": len(tracks[packet.target_model].pending_packets) + 1,
            }
            tracks[packet.target_model].pending_packets.append((packet, event))
            events.append(event)

    def _metadata(self, tracks: dict[str, TrackState], packet_events: list[dict[str, Any]],
                  deterministic: dict[str, Any], *, best_model: str | None,
                  best_rank: tuple[int, int, int] | None, rounds: int,
                  cutoff_reached: bool, provider_requests: dict[str, int]) -> dict[str, Any]:
        physical_requests = sum(provider_requests.values())
        logical_dispatched = sum(
            max(0, provider_requests[model] - len(track.retry_events))
            for model, track in tracks.items()
        )
        return {
            "design_id": DESIGN_ID, "condition": self.condition, "uplift_policy": "H+D",
            "collaboration_strategy": self.strategy.strategy_id, "seed": self.seed,
            "scheduler": "independent-track-v1",
            "reasoning_effort_by_model": {model: "medium" for model in MODELS},
            "selected_model": best_model,
            "selection_reason": "accepted" if best_rank and best_rank[0] == 0 else "global_best_checkpoint",
            "max_calls_per_model": self.max_calls_per_model,
            "calls_attempted": sum(track.calls for track in tracks.values()),
            "calls_dispatched": logical_dispatched,
            "physical_requests": physical_requests,
            "cost_free_429_retries": sum(len(track.retry_events) for track in tracks.values()),
            "rounds": rounds, "max_track_rounds": rounds,
            "dispatch_cutoff_s": self.dispatch_cutoff_s,
            "dispatch_cutoff_reached": cutoff_reached, "deterministic": deterministic,
            "packet_events": packet_events,
            "tracks": {model: {
                "calls_attempted": track.calls,
                "calls_dispatched": max(
                    0, provider_requests[model] - len(track.retry_events)
                ),
                "physical_requests": provider_requests[model],
                "pending_peer_packets": len(track.pending_packets),
                "restarts": track.restarts,
                "attempts": [asdict(attempt) for attempt in track.attempts],
                "call_errors": track.call_errors, "retry_events": track.retry_events,
                "failure_memory_entries": len(track.failure_memory),
            } for model, track in tracks.items()},
        }

    def _checkpoint_metadata(self, track: TrackState, round_number: int,
                             candidate_hash: str) -> dict[str, Any]:
        return {
            "design_id": DESIGN_ID, "condition": self.condition,
            "collaboration_strategy": self.strategy.strategy_id,
            "model": track.model, "call": track.calls, "round": round_number,
            "candidate_sha256": candidate_hash,
        }

    @staticmethod
    def _error(exc: BaseException, call: int, phase: str, dispatched: bool) -> dict[str, Any]:
        return {"call": call, "phase": phase, "dispatched": dispatched,
                "type": type(exc).__name__, "message": str(exc)[:1000]}


def _env_int(name: str, default: int, minimum: int, maximum: int) -> int:
    try:
        value = int(os.environ.get(name, str(default)))
    except ValueError as exc:
        raise ValueError(f"{name} must be an integer") from exc
    if not minimum <= value <= maximum:
        raise ValueError(f"{name} must be between {minimum} and {maximum}")
    return value


def create_agent() -> CollaborationEngineV2Agent:
    if os.environ.get("COLLAB_DESIGN_ID", DESIGN_ID) != DESIGN_ID:
        raise ValueError(f"COLLAB_DESIGN_ID must be {DESIGN_ID}")
    condition = os.environ.get("COLLAB_CONDITION", "").strip()
    strategy_id = os.environ.get("COLLAB_STRATEGY", "").strip()
    if not condition or not strategy_id:
        raise ValueError("COLLAB_CONDITION and COLLAB_STRATEGY are required")
    packet_chars = _env_int("COLLAB_PEER_PACKET_CHARS", 6000, 1, 12000)
    raw_ceiling = os.environ.get("COLLAB_MAX_CALLS_PER_MODEL", "25")
    ceiling = None if raw_ceiling == "unlimited" else int(raw_ceiling)
    return CollaborationEngineV2Agent(
        strategy=create_strategy(strategy_id, packet_chars=packet_chars), condition=condition,
        max_calls_per_model=ceiling,
        generation_max_tokens=_env_int("COLLAB_GENERATION_MAX_TOKENS", 12000, 1000, 32000),
        temperature=float(os.environ.get("COLLAB_TEMPERATURE", "0.2")),
        seed=_env_int("COLLAB_SEED", 1, 0, 2**31 - 1),
        max_restarts=_env_int("COLLAB_MAX_RESTARTS", 2, 1, 2),
        diagnostic_chars=_env_int("COLLAB_DIAGNOSTIC_CHARS", 6000, 500, 12000),
        failure_memory_chars=_env_int("COLLAB_FAILURE_MEMORY_CHARS", 3000, 500, 6000),
        peer_packet_chars=packet_chars,
        dispatch_cutoff_s=float(os.environ.get("COLLAB_DISPATCH_CUTOFF_S", "960")),
        max_cost_free_429_retries=_env_int("COLLAB_MAX_FREE_429_RETRIES", 2, 0, 5),
    )
