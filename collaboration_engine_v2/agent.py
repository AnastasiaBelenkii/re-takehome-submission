"""Frozen two-model base with C0/C1/C2 packet-only treatments."""

from __future__ import annotations

import asyncio
import math
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
from .salvage import compiles_with_sorry, contains_sorry, propose_sorrifications
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
    salvage_attempted: bool = False
    salvage_compiled: bool = False
    salvage_mode: str | None = None
    salvage_sha256: str | None = None
    salvage_retained_lines: int = 0


@dataclass
class VerificationJob:
    source: str
    candidate_sha256: str
    track: "TrackState"
    record: AttemptRecord
    call_round: int


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
    salvage_events: list[dict[str, Any]] = field(default_factory=list)
    peer_packets_consumed: int = 0
    reserve_release_reason: str | None = None
    active: bool = True


class CollaborationEngineV2Agent:
    def __init__(
        self, *, strategy: CollaborationStrategy, condition: str = "test",
        max_calls_per_model: int | None = 25, generation_max_tokens: int = 12000,
        temperature: float = 0.2, seed: int = 1, max_restarts: int = 2,
        diagnostic_chars: int = 6000, failure_memory_chars: int = 3000,
        peer_packet_chars: int = 6000, dispatch_cutoff_s: float = 960,
        max_cost_free_429_retries: int = 2, retry_backoff_s: float = 1.0,
        enable_salvage: bool = False, salvage_check_timeout_s: int = 2,
        model_call_wall_timeout_s: float = 420,
        fast_track_reserved_calls: int = 0,
        reserve_release_margin_s: float = 120,
        models: tuple[str, ...] = MODELS,
        clock: Callable[[], float] = time.monotonic,
    ) -> None:
        if not models or len(models) != len(set(models)):
            raise ValueError("models must be a non-empty tuple of unique model IDs")
        if max_calls_per_model is not None and not 1 <= max_calls_per_model <= 25:
            raise ValueError("max_calls_per_model must be 1..25 or None")
        if not 1 <= max_restarts <= 2:
            raise ValueError("max_restarts must be between 1 and 2")
        if not 0 <= max_cost_free_429_retries <= 5:
            raise ValueError("max_cost_free_429_retries must be between 0 and 5")
        if dispatch_cutoff_s <= 0:
            raise ValueError("dispatch_cutoff_s must be positive")
        if not math.isfinite(model_call_wall_timeout_s) or model_call_wall_timeout_s <= 0:
            raise ValueError("model_call_wall_timeout_s must be positive")
        if not 0 <= fast_track_reserved_calls <= 4:
            raise ValueError("fast_track_reserved_calls must be between 0 and 4")
        if max_calls_per_model is not None and fast_track_reserved_calls >= max_calls_per_model:
            raise ValueError("fast_track_reserved_calls must be below the call ceiling")
        if not math.isfinite(reserve_release_margin_s) or reserve_release_margin_s <= 0:
            raise ValueError("reserve_release_margin_s must be positive")
        if fast_track_reserved_calls and reserve_release_margin_s >= dispatch_cutoff_s:
            raise ValueError("reserve_release_margin_s must be below dispatch_cutoff_s")
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
        self.enable_salvage = enable_salvage
        self.salvage_check_timeout_s = salvage_check_timeout_s
        self.model_call_wall_timeout_s = model_call_wall_timeout_s
        self.fast_track_reserved_calls = fast_track_reserved_calls
        self.reserve_release_margin_s = reserve_release_margin_s
        self.models = tuple(models)
        self.clock = clock

    def _has_capacity(self, track: TrackState) -> bool:
        return track.active and (
            self.max_calls_per_model is None or track.calls < self.max_calls_per_model
        )

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        started = self.clock()
        tracks = {model: TrackState(model=model, candidate=problem.challenge) for model in self.models}
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
                # A complete warm-valid model proposal must always outrank a
                # deterministic candidate that Lean rejected, independent of
                # diagnostic counts.
                rank = (2, 1 if check.timed_out else 0, len(check.messages))
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
                    verification_events=[],
                ))

        cutoff_reached = False
        observations_by_round: dict[int, dict[str, TrackObservation]] = {}
        pending: dict[
            asyncio.Task,
            tuple[TrackState, str, PeerPacket | None, dict[str, Any] | None, int],
        ] = {}
        verification_task: asyncio.Task | None = None
        verification_job: VerificationJob | None = None
        queued_verification: VerificationJob | None = None
        verification_results: dict[str, dict[str, Any]] = {}
        verification_events: list[dict[str, Any]] = []
        owner_task = asyncio.current_task()

        def cancel_children_if_owner_cancelled(task: asyncio.Task) -> None:
            if task.cancelled():
                for child in tuple(pending):
                    child.cancel()
                if verification_task is not None:
                    verification_task.cancel()

        if owner_task is not None:
            owner_task.add_done_callback(cancel_children_if_owner_cancelled)

        def schedule(track: TrackState, *, check_cutoff: bool = True) -> bool:
            nonlocal cutoff_reached
            if not self._has_capacity(track):
                return False
            if (
                track.model == self.models[0]
                and self.fast_track_reserved_calls
                and self.max_calls_per_model is not None
                and track.calls >= self.max_calls_per_model - self.fast_track_reserved_calls
                and not track.pending_packets
            ):
                peer = tracks[self.models[1]]
                deadline_release = (
                    self.clock() - started
                    >= self.dispatch_cutoff_s - self.reserve_release_margin_s
                )
                peer_in_flight = any(
                    pending_value[0].model == peer.model
                    for pending_value in pending.values()
                )
                peer_exhausted = not self._has_capacity(peer) and not peer_in_flight
                if not deadline_release and not peer_exhausted:
                    return False
                if track.reserve_release_reason is None:
                    track.reserve_release_reason = (
                        "deadline_margin" if deadline_release else "peer_exhausted"
                    )
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
                if packet.kind == "progress-fill-event-latest-v2":
                    # A peer fill is its own task. In particular, do not carry
                    # a local restart instruction that tells the receiver to
                    # abandon the compiling skeleton it is about to receive.
                    phase = "peer_fill"
            track.calls += 1
            call_round = track.calls
            if packet_event is not None:
                track.peer_packets_consumed += 1
                packet_event["used_on_call"] = track.calls
                packet_event["used_on_round"] = call_round
                packet_event["used_at_s"] = round(self.clock() - started, 6)
                if "produced_at_s" in packet_event:
                    packet_event["delivery_delay_s"] = round(
                        packet_event["used_at_s"] - packet_event["produced_at_s"], 6
                    )
            task = asyncio.create_task(
                self._call_with_deadline(track, problem, phase, packet, services)
            )
            pending[task] = (track, phase, packet, packet_event, call_round)
            return True

        def start_verification(job: VerificationJob) -> None:
            nonlocal verification_task, verification_job
            verification_job = job
            verification_task = asyncio.create_task(
                self._verify_if_promising(job.source, True, services)
            )
            verification_events.append({
                "event": "started", "candidate_sha256": job.candidate_sha256,
                "model": job.track.model, "call": job.call_round,
            })

        def enqueue_verification(job: VerificationJob) -> bool:
            nonlocal queued_verification
            cached = verification_results.get(job.candidate_sha256)
            if cached is not None:
                return self._apply_verification(
                    job, cached, services, verification_events, cached=True
                )
            if verification_job is not None and verification_job.candidate_sha256 == job.candidate_sha256:
                verification_events.append({
                    "event": "deduplicated_active", "candidate_sha256": job.candidate_sha256,
                    "model": job.track.model, "call": job.call_round,
                })
                return False
            if queued_verification is not None:
                if queued_verification.candidate_sha256 == job.candidate_sha256:
                    verification_events.append({
                        "event": "deduplicated_queued", "candidate_sha256": job.candidate_sha256,
                        "model": job.track.model, "call": job.call_round,
                    })
                    return False
                verification_events.append({
                    "event": "superseded", "candidate_sha256": queued_verification.candidate_sha256,
                    "model": queued_verification.track.model,
                    "call": queued_verification.call_round,
                    "superseded_by_sha256": job.candidate_sha256,
                })
            queued_verification = job
            verification_events.append({
                "event": "queued", "candidate_sha256": job.candidate_sha256,
                "model": job.track.model, "call": job.call_round,
            })
            return False

        def advance_verification_queue() -> None:
            nonlocal queued_verification
            if verification_task is None and queued_verification is not None:
                job = queued_verification
                queued_verification = None
                start_verification(job)

        if self.clock() - started >= self.dispatch_cutoff_s:
            cutoff_reached = True
        else:
            for model in self.models:
                schedule(tracks[model], check_cutoff=False)

        verified_success = False
        while pending or verification_task is not None or queued_verification is not None:
            advance_verification_queue()
            waiters = tuple(pending) + ((verification_task,) if verification_task is not None else ())
            completed, _still_pending = await asyncio.wait(
                waiters, return_when=asyncio.FIRST_COMPLETED
            )
            if verification_task is not None and verification_task in completed:
                assert verification_job is not None
                job = verification_job
                try:
                    compatibility = verification_task.result()
                except asyncio.CancelledError:
                    raise
                except Exception as exc:
                    compatibility = {
                        "passed": False,
                        "verification_error": f"{type(exc).__name__}: {exc}"[:1000],
                    }
                verification_results[job.candidate_sha256] = compatibility
                verified_success = self._apply_verification(
                    job, compatibility, services, verification_events
                ) or verified_success
                if verified_success:
                    best_candidate, best_model, best_rank = (
                        job.source, job.track.model, (0, 0, 0)
                    )
                verification_task = None
                verification_job = None
                if verified_success and queued_verification is not None:
                    verification_events.append({
                        "event": "superseded_by_verified_success",
                        "candidate_sha256": queued_verification.candidate_sha256,
                        "model": queued_verification.track.model,
                        "call": queued_verification.call_round,
                    })
                    queued_verification = None
                else:
                    advance_verification_queue()
            ready_to_schedule: list[TrackState] = []
            completed_observation_rounds: set[int] = set()
            ordered_completed = sorted(
                (task for task in completed if task in pending),
                key=lambda task: self.models.index(pending[task][0].model),
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
                lean_accepted = False
                check = None
                if contract_ok:
                    check = await services.lean.check_file(proposal)
                    diagnostic_text, signature, raw_count = _diagnostics(check.messages, limit=self.diagnostic_chars)
                    lean_accepted, timed_out = bool(check.accepted), bool(check.timed_out)
                    accepted = False
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
                    1 if lean_accepted else (2 if contract_ok else 3),
                    1 if timed_out else 0,
                    raw_count,
                )
                checkpoint_saved = (
                    contract_ok
                    and not contains_sorry(proposal)
                    and (best_rank is None or rank < best_rank)
                )
                if checkpoint_saved:
                    best_rank, best_candidate, best_model = rank, proposal, track.model
                    checkpoint_metadata = self._checkpoint_metadata(
                        track, call_round, candidate_hash
                    )
                    checkpoint_metadata["compatibility_status"] = (
                        "provisional_warm_lean_passed" if lean_accepted
                        else "provisional_lean_failure"
                    )
                    services.checkpoint(best_candidate, checkpoint_metadata)
                record = AttemptRecord(
                    len(track.attempts) + 1, track.calls, call_round, phase,
                    candidate_hash, signature, lean_accepted, accepted,
                    False, False,
                    timed_out, raw_count,
                    diagnostic_text, checkpoint_saved, packet is not None,
                    declarations_ok, original_imports_ok, imports_normalized, contract_ok,
                )
                track.attempts.append(record)
                if lean_accepted:
                    if enqueue_verification(VerificationJob(
                        proposal, candidate_hash, track, record, call_round
                    )):
                        verified_success = True
                        best_candidate, best_model, best_rank = (
                            proposal, track.model, (0, 0, 0)
                        )
                track.restart_pending = False
                packet_candidate = track.candidate
                progress_candidate = None
                residual_goals = ""
                progress_sha256 = None
                if (
                    self.enable_salvage and contract_ok and check is not None
                    and not lean_accepted and not timed_out and not contains_sorry(proposal)
                ):
                    record.salvage_attempted = True
                    salvage = await self._attempt_salvage(
                        proposal, check.messages, track, services
                    )
                    if salvage is not None:
                        progress_candidate = salvage["source"]
                        residual_goals = salvage["residual_goals"]
                        progress_sha256 = salvage["sha256"]
                        record.salvage_compiled = True
                        record.salvage_mode = salvage["mode"]
                        record.salvage_sha256 = progress_sha256
                        record.salvage_retained_lines = salvage["retained_lines"]
                        track.candidate = progress_candidate
                observation = TrackObservation(
                    track.model, call_round, track.calls, packet_candidate,
                    diagnostic_text, accepted, timed_out,
                    progress_candidate, residual_goals, progress_sha256,
                )
                observations_by_round.setdefault(call_round, {})[track.model] = observation
                completed_observation_rounds.add(call_round)
                immediate_packets = tuple(self.strategy.after_observation(observation))
                self._install_packets(
                    immediate_packets, tracks, call_round, packet_events,
                    latest_wins=True, elapsed_s=self.clock() - started,
                )
                verified_success = verified_success or accepted
                if not accepted:
                    if lean_accepted:
                        track.feedback = (
                            "Warm Lean accepted this complete proposal and fresh verification "
                            "is pending. Continue with an independent complete alternative; "
                            "do not assume the pending candidate is holdout-compatible."
                        )
                    elif progress_candidate is not None:
                        track.feedback = (
                            "Warm Lean validated the current file up to explicit `sorry` "
                            "holes. Preserve its compiling structure and replace every "
                            "`sorry` with a complete proof. Residual goals:\n" + residual_goals
                        )
                    else:
                        track.feedback = diagnostic_text or (
                            "Lean timed out while checking the candidate." if timed_out
                            else "Lean rejected the candidate without a diagnostic message."
                        )
                    self._update_decomposition(track, signature, repeated, problem.challenge)
                    ready_to_schedule.append(track)

            for completed_round in sorted(completed_observation_rounds):
                paired = observations_by_round.get(completed_round, {})
                if len(paired) != len(self.models):
                    continue
                observations = tuple(paired[model] for model in self.models)
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
                    busy_models = {value[0].model for value in pending.values()}
                    for model in dict.fromkeys(track.model for track in ready_to_schedule):
                        track = tracks[model]
                        if track.model not in busy_models:
                            schedule(track, check_cutoff=False)

            # A track held at its reserve is not attached to a pending task.
            # Reconsider it whenever its peer completes and may have produced a
            # packet, exhausted its calls, or advanced the deadline clock.
            if not verified_success and self.clock() - started < self.dispatch_cutoff_s:
                busy_models = {value[0].model for value in pending.values()}
                for model in self.models:
                    if model not in busy_models:
                        schedule(tracks[model], check_cutoff=False)

        round_number = max((track.calls for track in tracks.values()), default=0)

        if owner_task is not None:
            owner_task.remove_done_callback(cancel_children_if_owner_cancelled)

        return AgentResult(best_candidate, self._metadata(
            tracks, packet_events, deterministic, best_model=best_model,
            best_rank=best_rank, rounds=round_number, cutoff_reached=cutoff_reached,
            provider_requests=self._provider_requests(services),
            verification_events=verification_events,
        ))

    def _provider_requests(self, services: Services) -> dict[str, int]:
        raw = getattr(services.llm, "requests_dispatched_by_model", {})
        return {model: int(raw.get(model, 0)) for model in self.models}

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

    def _apply_verification(
        self, job: VerificationJob, compatibility: dict[str, Any],
        services: Services, events: list[dict[str, Any]], *, cached: bool = False,
    ) -> bool:
        passed = bool(compatibility.get("passed"))
        job.record.compatibility_checked = True
        job.record.compatibility_passed = passed
        job.record.accepted = passed
        if not passed:
            job.record.diagnostic_excerpt = self._compatibility_diagnostic(compatibility)
            job.record.error_signature_sha256 = _sha256(job.record.diagnostic_excerpt)
            job.record.raw_diagnostic_count = 1
        else:
            job.record.checkpoint_saved = True
            metadata = self._checkpoint_metadata(
                job.track, job.call_round, job.candidate_sha256
            )
            metadata["compatibility_status"] = "fresh_comparator_passed"
            services.checkpoint(job.source, metadata)
        events.append({
            "event": "completed_cached" if cached else "completed",
            "candidate_sha256": job.candidate_sha256,
            "model": job.track.model, "call": job.call_round,
            "passed": passed,
            "comparator_timed_out": bool(compatibility.get("comparator_timed_out")),
            "verification_error": compatibility.get("verification_error"),
        })
        return passed

    async def _attempt_salvage(
        self, proposal: str, messages: list[dict[str, Any]],
        track: TrackState, services: Services,
    ) -> dict[str, Any] | None:
        candidates = propose_sorrifications(
            proposal, messages, residual_chars=self.diagnostic_chars
        )
        if not candidates:
            track.salvage_events.append({
                "attempted": True, "compiled": False,
                "reason": "no_safe_source_transformation",
                "parent_sha256": _sha256(_normalized_candidate(proposal)),
            })
            return None
        meaningful = [candidate for candidate in candidates if candidate.retained_lines > 0]
        if not meaningful:
            track.salvage_events.append({
                "attempted": True, "compiled": False,
                "reason": "no_retained_proof_structure",
                "parent_sha256": _sha256(_normalized_candidate(proposal)),
            })
            return None
        for index, candidate in enumerate(meaningful, start=1):
            check = await services.lean.check_file(
                candidate.source, timeout_s=self.salvage_check_timeout_s
            )
            event = {
                "attempted": True,
                "candidate_index": index,
                "mode": candidate.mode,
                "compiled": compiles_with_sorry(candidate.source, check),
                "timed_out": bool(check.timed_out),
                "duration_ms": int(check.duration_ms),
                "raw_diagnostic_count": len(check.messages),
                "retained_lines": candidate.retained_lines,
                "declaration_line": candidate.declaration_line,
                "error_line": candidate.error_line,
                "parent_sha256": _sha256(_normalized_candidate(proposal)),
                "skeleton_sha256": _sha256(_normalized_candidate(candidate.source)),
            }
            track.salvage_events.append(event)
            if event["compiled"]:
                return {
                    "source": candidate.source,
                    "mode": candidate.mode,
                    "retained_lines": candidate.retained_lines,
                    "residual_goals": candidate.residual_goals,
                    "sha256": event["skeleton_sha256"],
                }
        return None

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

    async def _call_with_deadline(
        self, track: TrackState, problem: Problem, phase: str,
        packet: PeerPacket | None, services: Services,
    ):
        # httpx read timeouts apply to individual socket reads, not the whole
        # request. This outer deadline bounds one semantic call including any
        # explicitly cost-free retries. Cancellation is deliberately allowed
        # to reach LLMClient, which marks the reservation's spend as unknown.
        async with asyncio.timeout(self.model_call_wall_timeout_s):
            return await self._call(track, problem, phase, packet, services)

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
            heading = (
                "Warm-checked partial skeleton to complete; replace every `sorry` while "
                "preserving verified structure:"
                if contains_sorry(track.candidate) else "Current candidate to repair:"
            )
            user.extend(["", heading, "```lean", track.candidate, "```"])
        if track.feedback:
            user.extend(["", "Bounded deduplicated Lean diagnostics:", "```text", track.feedback, "```"])
        if track.failure_memory:
            user.extend(["", "Bounded failed-approach memory (do not repeat these strategies):", "```text", "\n".join(track.failure_memory), "```"])
        if packet is not None:
            if packet.kind == "progress-fill-event-latest-v2":
                user.extend([
                    "",
                    "Compiler-validated peer skeleton: fill its residual holes now.",
                    "Preserve its compiling declarations and helper proofs. Replace every explicit `sorry` with complete Lean code; return one complete file without `sorry`. Do not critique, summarize, or restart from scratch unless Lean diagnostics prove the skeleton unusable.",
                    "```text", packet.content, "```",
                ])
            else:
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
                         round_number: int, events: list[dict[str, Any]],
                         latest_wins: bool = False,
                         elapsed_s: float | None = None) -> None:
        targets: set[str] = set()
        for packet in packets:
            if packet.target_model not in tracks or packet.source_model not in tracks:
                raise ValueError("strategy returned a packet for an unknown model")
            if packet.target_model == packet.source_model or packet.target_model in targets:
                raise ValueError("strategy packets must be one cross-model packet per target")
            if not packet.content.strip() or len(packet.content) > self.peer_packet_chars:
                raise ValueError("strategy packet is empty or oversized")
            targets.add(packet.target_model)
            pending = tracks[packet.target_model].pending_packets
            if latest_wins and pending:
                for _old_packet, old_event in pending:
                    old_event["replaced_before_use"] = True
                pending.clear()
            event = {
                "after_round": round_number, "target_model": packet.target_model,
                "source_model": packet.source_model, "kind": packet.kind,
                "content_chars": len(packet.content), "content_sha256": _sha256(packet.content),
                "queue_position": len(pending) + 1,
            }
            if elapsed_s is not None:
                event["produced_at_s"] = round(elapsed_s, 6)
            pending.append((packet, event))
            events.append(event)

    def _metadata(self, tracks: dict[str, TrackState], packet_events: list[dict[str, Any]],
                  deterministic: dict[str, Any], *, best_model: str | None,
                  best_rank: tuple[int, int, int] | None, rounds: int,
                  cutoff_reached: bool, provider_requests: dict[str, int],
                  verification_events: list[dict[str, Any]]) -> dict[str, Any]:
        physical_requests = sum(provider_requests.values())
        logical_dispatched = sum(
            max(0, provider_requests[model] - len(track.retry_events))
            for model, track in tracks.items()
        )
        return {
            "design_id": DESIGN_ID, "condition": self.condition, "uplift_policy": "H+D",
            "collaboration_strategy": self.strategy.strategy_id, "seed": self.seed,
            "scheduler": "independent-track-v1",
            "salvage_enabled": self.enable_salvage,
            "reasoning_effort_by_model": {model: "medium" for model in self.models},
            "selected_model": best_model,
            "selection_reason": "accepted" if best_rank and best_rank[0] == 0 else "global_best_checkpoint",
            "max_calls_per_model": self.max_calls_per_model,
            "calls_attempted": sum(track.calls for track in tracks.values()),
            "calls_dispatched": logical_dispatched,
            "physical_requests": physical_requests,
            "cost_free_429_retries": sum(len(track.retry_events) for track in tracks.values()),
            "rounds": rounds, "max_track_rounds": rounds,
            "dispatch_cutoff_s": self.dispatch_cutoff_s,
            "model_call_wall_timeout_s": self.model_call_wall_timeout_s,
            "fast_track_reserved_calls": self.fast_track_reserved_calls,
            "reserve_release_margin_s": self.reserve_release_margin_s,
            "dispatch_cutoff_reached": cutoff_reached, "deterministic": deterministic,
            "packet_events": packet_events,
            "verification_policy": "single-flight-latest-v1",
            "verification_events": verification_events,
            "tracks": {model: {
                "calls_attempted": track.calls,
                "calls_dispatched": max(
                    0, provider_requests[model] - len(track.retry_events)
                ),
                "physical_requests": provider_requests[model],
                "pending_peer_packets": len(track.pending_packets),
                "peer_packets_consumed": track.peer_packets_consumed,
                "reserve_release_reason": track.reserve_release_reason,
                "restarts": track.restarts,
                "attempts": [asdict(attempt) for attempt in track.attempts],
                "call_errors": track.call_errors, "retry_events": track.retry_events,
                "failure_memory_entries": len(track.failure_memory),
                "salvage_events": track.salvage_events,
            } for model, track in tracks.items()},
        }

    def _checkpoint_metadata(self, track: TrackState, round_number: int,
                             candidate_hash: str) -> dict[str, Any]:
        return {
            "design_id": DESIGN_ID, "condition": self.condition,
            "collaboration_strategy": self.strategy.strategy_id,
            "model": track.model, "call": round_number, "round": round_number,
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
        strategy=create_strategy(strategy_id, packet_chars=packet_chars, models=MODELS), condition=condition,
        models=MODELS,
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
        enable_salvage=os.environ.get("COLLAB_ENABLE_SALVAGE", "0") == "1",
        salvage_check_timeout_s=_env_int(
            "COLLAB_SALVAGE_CHECK_TIMEOUT_S", 2, 1, 120
        ),
        model_call_wall_timeout_s=float(
            os.environ.get("COLLAB_MODEL_CALL_WALL_TIMEOUT_S", "420")
        ),
        fast_track_reserved_calls=_env_int(
            "COLLAB_FAST_TRACK_RESERVED_CALLS", 0, 0, 4
        ),
        reserve_release_margin_s=float(
            os.environ.get("COLLAB_RESERVE_RELEASE_MARGIN_S", "120")
        ),
    )
