"""Independent repair portfolio matched to the supplied solo baseline.

Each model runs the baseline's chronological Lean-feedback repair policy on its
own candidate. Model calls in a round are concurrent, but Lean checks are
serialized because both tracks share the problem's Lean service. No candidate,
compiler message, or model response crosses between tracks.
"""

from __future__ import annotations

import asyncio
from dataclasses import asdict, dataclass, field
from typing import Any

from baselines.simple_agent import (
    Attempt,
    SimpleBaselineAgent,
    _extract_lean,
    _format_messages,
)
from re_harness import AgentResult, Problem, Services
from re_harness.models import MODEL_A, MODEL_B


DESIGN_ID = "independent-repair-portfolio-v1"


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
    ) -> None:
        self._agents = (
            SimpleBaselineAgent(
                model=MODEL_A,
                max_turns=max_turns,
                max_tokens=max_tokens,
                temperature=temperature,
            ),
            SimpleBaselineAgent(
                model=MODEL_B,
                max_turns=max_turns,
                max_tokens=max_tokens,
                temperature=temperature,
            ),
        )

    @staticmethod
    def _metadata(
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
            "rounds_started": rounds_started,
            "selected_model": selected_model,
            "selection_reason": selection_reason,
            "fixed_model_order": [MODEL_A, MODEL_B],
            "tracks": {
                track.model: {
                    "max_turns": track.agent.max_turns,
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

        for turn in range(1, max_turns + 1):
            active = [
                track
                for track in tracks
                if not track.disabled and turn <= track.agent.max_turns
            ]
            if not active:
                break
            rounds_started = turn

            async def propose(track: _Track):
                return await services.llm.complete(
                    model=track.model,
                    messages=track.agent._messages(
                        problem,
                        feedback=track.feedback,
                        turn=turn,
                        is_last=turn == track.agent.max_turns,
                    ),
                    max_tokens=track.agent.max_tokens,
                    temperature=track.agent.temperature,
                )

            responses = await asyncio.gather(
                *(propose(track) for track in active), return_exceptions=True
            )
            candidates_to_check: list[_Track] = []
            for track, response in zip(active, responses, strict=True):
                if isinstance(response, BaseException):
                    track.call_errors.append(
                        {
                            "turn": turn,
                            "type": type(response).__name__,
                            "message": str(response)[:1000],
                        }
                    )
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


def create_agent() -> SubmissionAgent:
    return SubmissionAgent()
