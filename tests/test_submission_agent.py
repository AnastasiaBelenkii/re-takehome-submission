from __future__ import annotations

import pytest

from re_harness import Problem
from re_harness.models import MODEL_A, MODEL_B
from submission.agent import DESIGN_ID, SubmissionAgent


class FakeResponse:
    def __init__(self, content: str):
        self.content = content


class FakeLLM:
    def __init__(self, responses):
        self.responses = responses
        self.requests = []

    async def complete(self, **kwargs):
        self.requests.append(kwargs)
        response = self.responses[kwargs["model"]]
        if isinstance(response, BaseException):
            raise response
        return FakeResponse(response)


class FakeCheck:
    def __init__(self, accepted: bool):
        self.accepted = accepted
        self.timed_out = False
        self.messages = [] if accepted else [{"severity": "error", "data": "bad proof"}]


class FakeLean:
    def __init__(self, accepted_by_source):
        self.accepted_by_source = accepted_by_source

    async def check_file(self, source: str):
        return FakeCheck(self.accepted_by_source[source])


class FakeServices:
    def __init__(self, llm, lean):
        self.llm = llm
        self.lean = lean
        self.checkpoints = []

    def checkpoint(self, source, metadata=None):
        self.checkpoints.append((source, metadata or {}))


@pytest.mark.asyncio
async def test_independent_identical_prompts_and_lean_selects_model_b():
    problem = Problem(
        id="p",
        description="prove True",
        challenge="import Mathlib\n\ntheorem p : True := by\n  sorry\n",
    )
    source_a = "import Mathlib\n\ntheorem p : True := by\n  exact False.elim (by contradiction)\n"
    source_b = "import Mathlib\n\ntheorem p : True := by\n  trivial\n"
    llm = FakeLLM({MODEL_A: source_a, MODEL_B: source_b})
    services = FakeServices(llm, FakeLean({source_a: False, source_b: True}))

    result = await SubmissionAgent().solve(problem, services)

    assert result.solution == source_b
    assert result.metadata["design_id"] == DESIGN_ID
    assert result.metadata["selected_model"] == MODEL_B
    assert {request["model"] for request in llm.requests} == {MODEL_A, MODEL_B}
    prompts = [request["messages"] for request in llm.requests]
    assert prompts[0] == prompts[1]


@pytest.mark.asyncio
async def test_fixed_model_a_fallback_when_neither_candidate_passes():
    problem = Problem(id="p", description="prove False", challenge="import Mathlib\n")
    source_a = "import Mathlib\n-- a\n"
    source_b = "import Mathlib\n-- b\n"
    services = FakeServices(
        FakeLLM({MODEL_A: source_a, MODEL_B: source_b}),
        FakeLean({source_a: False, source_b: False}),
    )

    result = await SubmissionAgent().solve(problem, services)

    assert result.solution == source_a
    assert result.metadata["selection_reason"] == "fixed_model_a_fallback"
