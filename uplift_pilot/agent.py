"""Problem-agnostic solo policies for the uplift pilot.

The judged ``submission`` package deliberately does not import this module.
Pilot conditions select this agent explicitly through the harness ``--agent``
option and configure it from a validated condition manifest.
"""

from __future__ import annotations

import hashlib
import os
import re
from dataclasses import asdict, dataclass
from typing import Any

from baselines.simple_agent import _extract_lean
from re_harness import AgentResult, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from uplift_pilot.constants import ALLOWED_MODELS, DESIGN_ID


POLICIES = frozenset({"P", "D"})
DEFAULT_DIAGNOSTIC_CHARS = 6000
DEFAULT_FAILURE_MEMORY_CHARS = 3000


def _env_int(name: str, default: int, *, minimum: int, maximum: int) -> int:
    raw = os.environ.get(name, str(default))
    try:
        value = int(raw)
    except ValueError as exc:
        raise ValueError(f"{name} must be an integer") from exc
    if not minimum <= value <= maximum:
        raise ValueError(f"{name} must be between {minimum} and {maximum}")
    return value


def _env_float(name: str, default: float, *, minimum: float, maximum: float) -> float:
    raw = os.environ.get(name, str(default))
    try:
        value = float(raw)
    except ValueError as exc:
        raise ValueError(f"{name} must be a number") from exc
    if not minimum <= value <= maximum:
        raise ValueError(f"{name} must be between {minimum} and {maximum}")
    return value


def _normalized_candidate(source: str) -> str:
    lines = [line.rstrip() for line in source.replace("\r\n", "\n").split("\n")]
    while lines and not lines[0]:
        lines.pop(0)
    while lines and not lines[-1]:
        lines.pop()
    return "\n".join(lines) + "\n"


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _normalize_message(message: dict[str, Any]) -> str:
    severity = str(message.get("severity", "message")).lower().strip()
    data = re.sub(r"\s+", " ", str(message.get("data", "")).strip())
    # Source positions can drift while the underlying failure stays unchanged.
    return f"{severity}:{data}"


def _diagnostics(messages: list[dict[str, Any]], *, limit: int) -> tuple[str, str, int]:
    normalized = [_normalize_message(message) for message in messages]
    signature = _sha256("\n".join(normalized))
    unique: list[str] = []
    seen: set[str] = set()
    for item in normalized:
        if item and item not in seen:
            seen.add(item)
            unique.append(item)
    text = "\n".join(unique)
    if len(text) > limit:
        text = text[: max(0, limit - 24)] + "\n...[diagnostics bounded]"
    return text, signature, len(messages)


@dataclass
class AttemptRecord:
    attempt: int
    call: int
    phase: str
    candidate_sha256: str
    error_signature_sha256: str
    accepted: bool
    timed_out: bool
    raw_diagnostic_count: int
    diagnostic_excerpt: str
    checkpoint_saved: bool
    restart_reason: str | None = None


class UpliftPilotAgent:
    """One-model repair loop implementing either P or D over common substrate H."""

    def __init__(
        self,
        *,
        model: str,
        policy: str,
        condition: str = "test",
        max_calls: int = 25,
        generation_max_tokens: int = 12000,
        planning_max_tokens: int = 2500,
        temperature: float = 0.2,
        max_restarts: int = 2,
        diagnostic_chars: int = DEFAULT_DIAGNOSTIC_CHARS,
        failure_memory_chars: int = DEFAULT_FAILURE_MEMORY_CHARS,
    ) -> None:
        if model not in ALLOWED_MODELS:
            raise ValueError(f"model is not allowed: {model}")
        if policy not in POLICIES:
            raise ValueError(f"policy must be one of {sorted(POLICIES)}")
        if not 1 <= max_calls <= 25:
            raise ValueError("max_calls must be between 1 and 25")
        if not 1 <= max_restarts <= 2:
            raise ValueError("max_restarts must be between 1 and 2")
        self.model = model
        self.policy = policy
        self.condition = condition
        self.max_calls = max_calls
        self.generation_max_tokens = generation_max_tokens
        self.planning_max_tokens = planning_max_tokens
        self.temperature = temperature
        self.max_restarts = max_restarts
        self.diagnostic_chars = diagnostic_chars
        self.failure_memory_chars = failure_memory_chars

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        calls = 0
        candidate = problem.challenge
        best_candidate = problem.challenge
        best_rank: tuple[int, int, int] | None = None
        feedback = ""
        memo = ""
        planning_fired = False
        restarts = 0
        restart_pending = False
        failure_memory: list[str] = []
        seen_candidates: set[str] = set()
        signature_run = 0
        previous_signature: str | None = None
        attempts: list[AttemptRecord] = []
        call_errors: list[dict[str, Any]] = []

        while calls < self.max_calls:
            phase = "direct" if not attempts else ("restart" if restart_pending else "repair")
            calls += 1
            try:
                response = await services.llm.complete(
                    model=self.model,
                    messages=self._generation_messages(
                        problem,
                        candidate=candidate,
                        feedback=feedback,
                        memo=memo,
                        phase=phase,
                        call=calls,
                        failure_memory=failure_memory,
                    ),
                    max_tokens=self.generation_max_tokens,
                    temperature=self.temperature,
                )
            except (BudgetAccountingError, BudgetExceeded) as exc:
                calls -= 1
                call_errors.append(
                    {"call": calls + 1, "phase": phase, "dispatched": False, "type": type(exc).__name__, "message": str(exc)[:1000]}
                )
                break
            except Exception as exc:
                call_errors.append(
                    {"call": calls, "phase": phase, "type": type(exc).__name__, "message": str(exc)[:1000]}
                )
                restart_pending = False
                continue

            candidate = _extract_lean(response.content, fallback=candidate)
            normalized = _normalized_candidate(candidate)
            candidate_hash = _sha256(normalized)
            repeated_candidate = candidate_hash in seen_candidates
            seen_candidates.add(candidate_hash)

            check = await services.lean.check_file(candidate)
            diagnostic_text, signature, raw_count = _diagnostics(
                check.messages, limit=self.diagnostic_chars
            )
            rank = (0 if check.accepted else 1, 1 if check.timed_out else 0, raw_count)
            checkpoint_saved = best_rank is None or rank < best_rank
            if checkpoint_saved:
                best_rank = rank
                best_candidate = candidate
                services.checkpoint(
                    best_candidate,
                    {
                        "design_id": DESIGN_ID,
                        "condition": self.condition,
                        "policy": self.policy,
                        "model": self.model,
                        "call": calls,
                        "candidate_sha256": candidate_hash,
                    },
                )

            attempt = AttemptRecord(
                attempt=len(attempts) + 1,
                call=calls,
                phase=phase,
                candidate_sha256=candidate_hash,
                error_signature_sha256=signature,
                accepted=bool(check.accepted),
                timed_out=bool(check.timed_out),
                raw_diagnostic_count=raw_count,
                diagnostic_excerpt=diagnostic_text,
                checkpoint_saved=checkpoint_saved,
            )
            attempts.append(attempt)
            restart_pending = False
            if check.accepted:
                best_candidate = candidate
                break

            feedback = diagnostic_text or (
                "Lean timed out while checking the candidate."
                if check.timed_out
                else "Lean rejected the candidate without a diagnostic message."
            )

            if self.policy == "P" and not planning_fired:
                if calls >= self.max_calls:
                    break
                planning_fired = True
                calls += 1
                try:
                    plan_response = await services.llm.complete(
                        model=self.model,
                        messages=self._planning_messages(problem, candidate, feedback),
                        max_tokens=self.planning_max_tokens,
                        temperature=self.temperature,
                    )
                    memo = plan_response.content[: self.failure_memory_chars]
                except (BudgetAccountingError, BudgetExceeded) as exc:
                    calls -= 1
                    planning_fired = False
                    call_errors.append(
                        {"call": calls + 1, "phase": "planning", "dispatched": False, "type": type(exc).__name__, "message": str(exc)[:1000]}
                    )
                    break
                except Exception as exc:
                    call_errors.append(
                        {
                            "call": calls,
                            "phase": "planning",
                            "type": type(exc).__name__,
                            "message": str(exc)[:1000],
                        }
                    )
                    memo = "Planning call failed; repair directly from the Lean feedback."
                continue

            if self.policy == "D":
                signature_run = signature_run + 1 if signature == previous_signature else 1
                previous_signature = signature
                reason = None
                if repeated_candidate:
                    reason = "repeated_normalized_candidate"
                elif signature_run >= 3:
                    reason = "unchanged_error_signature_two_transitions"
                if reason and restarts < self.max_restarts:
                    restarts += 1
                    attempts[-1].restart_reason = reason
                    failure_memory.append(
                        f"trajectory {restarts}: candidate {candidate_hash[:12]}, "
                        f"error {signature[:12]}: {feedback[:900]}"
                    )
                    joined = "\n".join(failure_memory)
                    while len(joined) > self.failure_memory_chars and len(failure_memory) > 1:
                        failure_memory.pop(0)
                        joined = "\n".join(failure_memory)
                    candidate = problem.challenge
                    feedback = ""
                    previous_signature = None
                    signature_run = 0
                    restart_pending = True

        metadata = {
            "design_id": DESIGN_ID,
            "condition": self.condition,
            "policy": self.policy,
            "model": self.model,
            "calls_dispatched": calls,
            "max_calls": self.max_calls,
            "planning_calls": 1 if planning_fired else 0,
            "planning_memo_sha256": _sha256(memo) if memo else None,
            "restarts": restarts,
            "max_restarts": self.max_restarts if self.policy == "D" else 0,
            "attempts": [asdict(attempt) for attempt in attempts],
            "call_errors": call_errors,
            "best_candidate_sha256": _sha256(_normalized_candidate(best_candidate)),
            "failure_memory_entries": len(failure_memory),
        }
        return AgentResult(best_candidate, metadata)

    def _generation_messages(
        self,
        problem: Problem,
        *,
        candidate: str,
        feedback: str,
        memo: str,
        phase: str,
        call: int,
        failure_memory: list[str],
    ) -> list[dict[str, str]]:
        system = [
            "Write one complete Lean 4 file using Mathlib.",
            "Return only Lean code, preferably in one ```lean block.",
            "Preserve all theorem names and statements from the pristine challenge.",
            "Do not use sorry, admit, axioms, or unsafe escapes.",
        ]
        if phase == "restart":
            system.append(
                "This is a diversified restart. Abandon the prior trajectory and use a materially different mathematical or Lean strategy."
            )
        user = [
            f"Problem id: {problem.id}",
            f"Policy: {self.policy}; dispatched call: {call}/{self.max_calls}; phase: {phase}",
            "",
            "Problem description:",
            problem.description,
            "",
            "Pristine Lean challenge:",
            "```lean",
            problem.challenge,
            "```",
        ]
        if phase != "direct" and phase != "restart":
            user.extend(["", "Current candidate to repair:", "```lean", candidate, "```"])
        if feedback:
            user.extend(["", "Bounded deduplicated Lean diagnostics:", "```text", feedback, "```"])
        if memo and self.policy == "P":
            user.extend(["", "Strategy memo to follow:", "```text", memo, "```"])
        if failure_memory and self.policy == "D":
            user.extend(
                ["", "Bounded failed-approach memory (do not repeat these strategies):", "```text", "\n".join(failure_memory), "```"]
            )
        return [
            {"role": "system", "content": "\n".join(system)},
            {"role": "user", "content": "\n".join(user)},
        ]

    @staticmethod
    def _planning_messages(problem: Problem, candidate: str, feedback: str) -> list[dict[str, str]]:
        return [
            {
                "role": "system",
                "content": (
                    "Produce a short structured strategy memo, not Lean source. Include: informal mathematical proof; "
                    "Lean proof architecture; useful subgoals or intermediate lemmas; likely tactics and Mathlib lemmas; "
                    "and diagnosis of the failed attempt."
                ),
            },
            {
                "role": "user",
                "content": "\n".join(
                    [
                        f"Problem: {problem.description}",
                        "Pristine challenge:",
                        problem.challenge,
                        "Failed candidate:",
                        candidate,
                        "Lean diagnostics:",
                        feedback,
                    ]
                ),
            },
        ]


def create_agent() -> UpliftPilotAgent:
    design = os.environ.get("UPLIFT_DESIGN_ID", DESIGN_ID)
    if design != DESIGN_ID:
        raise ValueError(f"UPLIFT_DESIGN_ID must be {DESIGN_ID}")
    model = os.environ.get("UPLIFT_MODEL", "").strip()
    policy = os.environ.get("UPLIFT_POLICY", "").strip().upper()
    condition = os.environ.get("UPLIFT_CONDITION", "").strip()
    if not condition:
        raise ValueError("UPLIFT_CONDITION is required")
    return UpliftPilotAgent(
        model=model,
        policy=policy,
        condition=condition,
        max_calls=_env_int("UPLIFT_MAX_CALLS", 25, minimum=1, maximum=25),
        generation_max_tokens=_env_int(
            "UPLIFT_GENERATION_MAX_TOKENS", 12000, minimum=1000, maximum=32000
        ),
        planning_max_tokens=_env_int(
            "UPLIFT_PLANNING_MAX_TOKENS", 2500, minimum=500, maximum=4000
        ),
        temperature=_env_float("UPLIFT_TEMPERATURE", 0.2, minimum=0.0, maximum=2.0),
        max_restarts=_env_int("UPLIFT_MAX_RESTARTS", 2, minimum=1, maximum=2),
        diagnostic_chars=_env_int(
            "UPLIFT_DIAGNOSTIC_CHARS", DEFAULT_DIAGNOSTIC_CHARS, minimum=500, maximum=12000
        ),
        failure_memory_chars=_env_int(
            "UPLIFT_FAILURE_MEMORY_CHARS", DEFAULT_FAILURE_MEMORY_CHARS, minimum=500, maximum=6000
        ),
    )
