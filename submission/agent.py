"""Independent repair portfolio matched to the supplied solo baseline.

Each model runs the baseline's chronological Lean-feedback repair policy on its
own candidate. Model calls in a round are concurrent, but Lean checks are
serialized because both tracks share the problem's Lean service. No candidate,
compiler message, or model response crosses between tracks.
"""

from __future__ import annotations

import asyncio
import itertools
from dataclasses import asdict, dataclass, field
from typing import Any

from baselines.simple_agent import (
    Attempt,
    SimpleBaselineAgent,
    _extract_lean,
    _format_messages,
)
from re_harness import AgentResult, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.llm import LLMCallError
from re_harness.models import MODEL_A, MODEL_B


DESIGN_ID = "independent-repair-portfolio-v1"
JUDGE_MAX_OUTPUT_TOKENS = 32000


@dataclass
class _Track:
    agent: SimpleBaselineAgent
    candidate: str
    feedback: str = ""
    attempts: list[Attempt] = field(default_factory=list)
    call_errors: list[dict[str, Any]] = field(default_factory=list)
    lean_errors: list[dict[str, Any]] = field(default_factory=list)
    disabled: bool = False

    @property
    def model(self) -> str:
        return self.agent.model


class SubmissionAgent:
    """Run two baseline-equivalent repair loops without communication."""

    def __init__(
        self,
        *,
        max_turns: int | None = None,
        max_tokens: int | None = None,
        temperature: float | None = None,
        external_limits_only: bool = False,
    ) -> None:
        if external_limits_only and (max_turns is not None or max_tokens is not None):
            raise ValueError(
                "external_limits_only cannot be combined with internal turn/token overrides"
            )
        self.external_limits_only = external_limits_only
        effective_max_tokens = (
            JUDGE_MAX_OUTPUT_TOKENS if external_limits_only else max_tokens
        )
        self._agents = (
            SimpleBaselineAgent(
                model=MODEL_A,
                max_turns=max_turns,
                max_tokens=effective_max_tokens,
                temperature=temperature,
            ),
            SimpleBaselineAgent(
                model=MODEL_B,
                max_turns=max_turns,
                max_tokens=effective_max_tokens,
                temperature=temperature,
            ),
        )

    def _metadata(
        self,
        tracks: list[_Track],
        *,
        selected_model: str,
        selection_reason: str,
        rounds_started: int,
    ) -> dict[str, Any]:
        return {
            "design_id": DESIGN_ID,
            "communication": "none",
            "repair_policy": "supplied-simple-baseline",
            "schedule": "parallel-model-calls-serialized-lean-checks",
            "resource_policy": (
                "external-wall-and-budget-limits-only"
                if self.external_limits_only
                else "internally-capped"
            ),
            "rounds_started": rounds_started,
            "selected_model": selected_model,
            "selection_reason": selection_reason,
            "fixed_model_order": [MODEL_A, MODEL_B],
            "tracks": {
                track.model: {
                    "max_turns": (
                        None if self.external_limits_only else track.agent.max_turns
                    ),
                    "max_tokens": track.agent.max_tokens,
                    "temperature": track.agent.temperature,
                    "attempts": [asdict(attempt) for attempt in track.attempts],
                    "call_errors": track.call_errors,
                    "lean_errors": track.lean_errors,
                    "disabled": track.disabled,
                }
                for track in tracks
            },
        }

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        tracks = [_Track(agent, problem.challenge) for agent in self._agents]
        max_turns = max(track.agent.max_turns for track in tracks)
        rounds_started = 0

        turns = (
            itertools.count(1)
            if self.external_limits_only
            else range(1, max_turns + 1)
        )
        for turn in turns:
            active = [
                track
                for track in tracks
                if not track.disabled
                and (self.external_limits_only or turn <= track.agent.max_turns)
            ]
            if not active:
                break
            rounds_started = turn

            async def propose(track: _Track):
                messages = track.agent._messages(
                    problem,
                    feedback=track.feedback,
                    turn=turn,
                    is_last=(
                        not self.external_limits_only
                        and turn == track.agent.max_turns
                    ),
                )
                if self.external_limits_only:
                    bounded_label = f"Baseline turn: {turn}/{track.agent.max_turns}"
                    external_label = (
                        f"Baseline turn: {turn}; external wall-clock and budget "
                        "limits govern"
                    )
                    messages[-1]["content"] = messages[-1]["content"].replace(
                        bounded_label, external_label, 1
                    )
                return await services.llm.complete(
                    model=track.model,
                    messages=messages,
                    max_tokens=track.agent.max_tokens,
                    temperature=track.agent.temperature,
                )

            responses = await asyncio.gather(
                *(propose(track) for track in active), return_exceptions=True
            )
            candidates_to_check: list[_Track] = []
            for track, response in zip(active, responses, strict=True):
                if isinstance(response, BaseException):
                    retryable = (
                        self.external_limits_only
                        and isinstance(response, LLMCallError)
                        and "reported no cost" in str(response)
                    )
                    track.call_errors.append(
                        {
                            "turn": turn,
                            "type": type(response).__name__,
                            "message": str(response)[:1000],
                            "retryable": retryable,
                        }
                    )
                    if isinstance(response, (BudgetAccountingError, BudgetExceeded)):
                        track.disabled = True
                    elif not retryable:
                        track.disabled = True
                    continue
                track.candidate = _extract_lean(
                    response.content, fallback=track.candidate
                )
                candidates_to_check.append(track)

            # Fixed model order makes selection deterministic when both models
            # produce accepted candidates in the same round.
            for track in tracks:
                if track not in candidates_to_check:
                    continue
                try:
                    check = await services.lean.check_file(track.candidate)
                except Exception as exc:
                    track.lean_errors.append(
                        {
                            "turn": turn,
                            "type": type(exc).__name__,
                            "message": str(exc)[:1000],
                        }
                    )
                    track.disabled = True
                    continue

                track.attempts.append(
                    Attempt(
                        turn=turn,
                        accepted=check.accepted,
                        timed_out=check.timed_out,
                        message_count=len(check.messages),
                    )
                )
                services.checkpoint(
                    track.candidate,
                    {
                        "design_id": DESIGN_ID,
                        "model": track.model,
                        "turn": turn,
                        "accepted_by_repl": check.accepted,
                    },
                )
                if check.accepted:
                    return AgentResult(
                        track.candidate,
                        self._metadata(
                            tracks,
                            selected_model=track.model,
                            selection_reason="first_lean_accepted_in_fixed_model_order",
                            rounds_started=rounds_started,
                        ),
                    )

                track.feedback = _format_messages(check.messages)
                if check.timed_out and not track.feedback:
                    track.feedback = (
                        "Lean timed out while checking the previous candidate."
                    )

        # A failed REPL check should agree with the final Comparator in normal
        # operation. Preserve a deterministic last candidate for timeout and
        # service-failure cases, preferring the first model that returned one.
        selected = next(
            (track for track in tracks if track.attempts),
            next((track for track in tracks if not track.disabled), tracks[0]),
        )
        return AgentResult(
            selected.candidate,
            self._metadata(
                tracks,
                selected_model=selected.model,
                selection_reason="fixed_model_order_fallback",
                rounds_started=rounds_started,
            ),
        )


def create_agent():
    """Create the promoted C1+ fill/reserve submission candidate."""

    # Keep the evaluator-facing module and factory stable while selecting the
    # experimentally frozen candidate without dispatch-only environment flags.
    from submission.candidates import create_c1plus_fill_reserve_agent

    return create_c1plus_fill_reserve_agent()
