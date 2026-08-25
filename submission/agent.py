"""Null collaboration control: independent one-shot proposals, then Lean selection."""

from __future__ import annotations

import asyncio
import re
from typing import Any

from re_harness import AgentResult, Problem, Services
from re_harness.models import MODEL_A, MODEL_B


DESIGN_ID = "independent-one-shot-portfolio-v1"
MAX_TOKENS = 12_000
TEMPERATURE = 0.2


def _extract_lean(text: str, fallback: str) -> str:
    fenced = re.findall(
        r"```(?:lean|lean4)?\s*\n(.*?)```", text, flags=re.DOTALL | re.IGNORECASE
    )
    if fenced:
        return fenced[-1].strip() + "\n"
    stripped = text.strip()
    import_at = stripped.find("import ")
    if import_at >= 0:
        return stripped[import_at:].strip() + "\n"
    return fallback


def _messages(problem: Problem) -> list[dict[str, str]]:
    return [
        {
            "role": "system",
            "content": (
                "You are writing a complete Lean 4 file using Mathlib. "
                "Return only the complete Lean code, preferably in one ```lean code block. "
                "Preserve every required declaration name and statement from the challenge. "
                "Do not use sorry, admit, axioms, or unsafe escapes. The file must compile as-is."
            ),
        },
        {
            "role": "user",
            "content": "\n".join(
                [
                    f"Problem id: {problem.id}",
                    "",
                    "Problem description:",
                    problem.description,
                    "",
                    "Challenge Lean file:",
                    "```lean",
                    problem.challenge,
                    "```",
                ]
            ),
        },
    ]


class SubmissionAgent:
    """Give both models the same task independently; permit no communication."""

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        messages = _messages(problem)

        async def propose(model: str):
            return await services.llm.complete(
                model=model,
                messages=messages,
                max_tokens=MAX_TOKENS,
                temperature=TEMPERATURE,
            )

        responses = await asyncio.gather(
            propose(MODEL_A), propose(MODEL_B), return_exceptions=True
        )

        candidates: dict[str, str] = {}
        call_errors: dict[str, dict[str, str]] = {}
        for model, response in zip((MODEL_A, MODEL_B), responses, strict=True):
            if isinstance(response, BaseException):
                candidates[model] = problem.challenge
                call_errors[model] = {
                    "type": type(response).__name__,
                    "message": str(response)[:1000],
                }
            else:
                candidates[model] = _extract_lean(response.content, problem.challenge)

        # Preserve Model A's proposal if the worker is interrupted during selection.
        services.checkpoint(
            candidates[MODEL_A], {"design_id": DESIGN_ID, "selection": "pending"}
        )

        checks: dict[str, Any] = {}
        for model in (MODEL_A, MODEL_B):
            checks[model] = await services.lean.check_file(candidates[model])

        accepted = [model for model in (MODEL_A, MODEL_B) if checks[model].accepted]
        if accepted:
            selected = accepted[0]
            selection_reason = "first_lean_accepted_in_fixed_model_order"
        elif MODEL_A not in call_errors:
            selected = MODEL_A
            selection_reason = "fixed_model_a_fallback"
        else:
            selected = MODEL_B
            selection_reason = "model_a_call_failed"

        metadata = {
            "design_id": DESIGN_ID,
            "communication": "none",
            "calls_per_model": 1,
            "max_tokens_per_call": MAX_TOKENS,
            "temperature": TEMPERATURE,
            "fixed_model_order": [MODEL_A, MODEL_B],
            "selected_model": selected,
            "selection_reason": selection_reason,
            "call_errors": call_errors,
            "lean_checks": {
                model: {
                    "accepted": check.accepted,
                    "timed_out": check.timed_out,
                    "message_count": len(check.messages),
                }
                for model, check in checks.items()
            },
        }
        return AgentResult(candidates[selected], metadata)


def create_agent() -> SubmissionAgent:
    return SubmissionAgent()
