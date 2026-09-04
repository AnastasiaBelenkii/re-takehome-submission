from __future__ import annotations

import asyncio

import pytest

from re_harness import Problem
from re_harness.models import MODEL_A, MODEL_B
from submission.agent import (
    DESIGN_ID,
    SubmissionAgent,
    create_agent,
)


class FakeResponse:
    def __init__(self, content: str):
        self.content = content


class FakeLLM:
    def __init__(self, responses):
        self.responses = {model: list(values) for model, values in responses.items()}
        self.requests = []
        self._in_flight = 0
        self.max_in_flight = 0

    async def complete(self, **kwargs):
        self.requests.append(kwargs)
        self._in_flight += 1
        self.max_in_flight = max(self.max_in_flight, self._in_flight)
        await asyncio.sleep(0)
        self._in_flight -= 1
        response = self.responses[kwargs["model"]].pop(0)
        if isinstance(response, BaseException):
            raise response
        return FakeResponse(response)


class FakeCheck:
    def __init__(self, accepted: bool, message: str = "bad proof"):
        self.accepted = accepted
        self.timed_out = False
        self.messages = [] if accepted else [{"severity": "error", "data": message}]


class FakeLean:
    def __init__(self, outcomes):
        self.outcomes = dict(outcomes)
        self.checked = []

    async def check_file(self, source: str):
        self.checked.append(source)
        result = self.outcomes[source]
        if isinstance(result, BaseException):
            raise result
        if isinstance(result, tuple):
            return FakeCheck(*result)
        return FakeCheck(result)


class FakeServices:
    def __init__(self, llm, lean):
        self.llm = llm
        self.lean = lean
        self.checkpoints = []

    def checkpoint(self, source, metadata=None):
        self.checkpoints.append((source, metadata or {}))


def problem() -> Problem:
    return Problem(
        id="p",
        description="prove True",
        challenge="import Mathlib\n\ntheorem p : True := by\n  sorry\n",
    )


@pytest.mark.asyncio
async def test_models_repair_independently_and_model_b_succeeds():
    q0 = "import Mathlib\n-- qwen initial\n"
    g0 = "import Mathlib\n-- gpt initial\n"
    q1 = "import Mathlib\n-- qwen repair\n"
    g1 = "import Mathlib\n\ntheorem p : True := by\n  trivial\n"
    llm = FakeLLM({MODEL_A: [q0, q1], MODEL_B: [g0, g1]})
    services = FakeServices(
        llm,
        FakeLean(
            {
                q0: (False, "QWEN_ONLY_ERROR"),
                g0: (False, "GPT_ONLY_ERROR"),
                q1: (False, "still wrong"),
                g1: True,
            }
        ),
    )

    result = await SubmissionAgent(max_turns=2).solve(problem(), services)

    assert result.solution == g1
    assert result.metadata["design_id"] == DESIGN_ID
    assert result.metadata["communication"] == "none"
    assert result.metadata["selected_model"] == MODEL_B
    assert llm.max_in_flight == 2

    second_q = [r for r in llm.requests if r["model"] == MODEL_A][1]
    second_g = [r for r in llm.requests if r["model"] == MODEL_B][1]
    q_prompt = str(second_q["messages"])
    g_prompt = str(second_g["messages"])
    assert "QWEN_ONLY_ERROR" in q_prompt and "GPT_ONLY_ERROR" not in q_prompt
    assert "GPT_ONLY_ERROR" in g_prompt and "QWEN_ONLY_ERROR" not in g_prompt


@pytest.mark.asyncio
async def test_both_models_are_called_before_fixed_order_accepted_selection():
    q0 = "import Mathlib\n-- qwen valid\n"
    g0 = "import Mathlib\n-- gpt also generated\n"
    llm = FakeLLM({MODEL_A: [q0], MODEL_B: [g0]})
    services = FakeServices(llm, FakeLean({q0: True, g0: True}))

    result = await SubmissionAgent(max_turns=1).solve(problem(), services)

    assert {request["model"] for request in llm.requests} == {MODEL_A, MODEL_B}
    assert result.solution == q0
    assert result.metadata["selected_model"] == MODEL_A
    assert services.lean.checked == [q0]


@pytest.mark.asyncio
async def test_one_model_call_failure_does_not_discard_other_model():
    g0 = "import Mathlib\n\ntheorem p : True := by\n  trivial\n"
    llm = FakeLLM({MODEL_A: [RuntimeError("rate limited")], MODEL_B: [g0]})
    services = FakeServices(llm, FakeLean({g0: True}))

    result = await SubmissionAgent(max_turns=2).solve(problem(), services)

    assert result.solution == g0
    assert result.metadata["selected_model"] == MODEL_B
    errors = result.metadata["tracks"][MODEL_A]["call_errors"]
    assert errors[0]["type"] == "RuntimeError"


@pytest.mark.asyncio
async def test_fixed_model_fallback_after_both_tracks_exhaust_repairs():
    q0 = "import Mathlib\n-- q0\n"
    g0 = "import Mathlib\n-- g0\n"
    q1 = "import Mathlib\n-- q1\n"
    g1 = "import Mathlib\n-- g1\n"
    llm = FakeLLM({MODEL_A: [q0, q1], MODEL_B: [g0, g1]})
    services = FakeServices(
        llm, FakeLean({source: False for source in (q0, g0, q1, g1)})
    )

    result = await SubmissionAgent(max_turns=2).solve(problem(), services)

    assert result.solution == q1
    assert result.metadata["selected_model"] == MODEL_A
    assert result.metadata["selection_reason"] == "fixed_model_order_fallback"
    assert len(result.metadata["tracks"][MODEL_A]["attempts"]) == 2
    assert len(result.metadata["tracks"][MODEL_B]["attempts"]) == 2


def test_judged_factory_uses_external_limits_only_but_experiments_do_not(monkeypatch):
    monkeypatch.setenv("VM_TIME_LIMIT_S", "28800")
    monkeypatch.delenv("COLLAB_MAX_CALLS_PER_MODEL", raising=False)
    monkeypatch.delenv("COLLAB_DISPATCH_CUTOFF_S", raising=False)
    judged = create_agent()
    experimental = SubmissionAgent()

    assert judged.condition == "c1plus-fill-reserve"
    assert judged.max_calls_per_model is None
    assert judged.dispatch_cutoff_s == 28080
    assert experimental.external_limits_only is False
    assert {agent.max_turns for agent in experimental._agents} == {25}


@pytest.mark.asyncio
async def test_external_limits_only_ignores_internal_turn_cap():
    q0, q1 = "import Mathlib\n-- q0\n", "import Mathlib\n-- q1\n"
    g0 = "import Mathlib\n-- g0\n"
    g1 = "import Mathlib\n\ntheorem p : True := by\n  trivial\n"
    llm = FakeLLM({MODEL_A: [q0, q1], MODEL_B: [g0, g1]})
    services = FakeServices(
        llm,
        FakeLean({q0: False, g0: False, q1: False, g1: True}),
    )
    agent = SubmissionAgent(external_limits_only=True)
    for track in agent._agents:
        track.max_turns = 1

    result = await agent.solve(problem(), services)

    assert result.solution == g1
    assert result.metadata["rounds_started"] == 2
    assert result.metadata["resource_policy"] == "external-wall-and-budget-limits-only"
    assert all(
        track["max_turns"] is None for track in result.metadata["tracks"].values()
    )
    second_round_prompt = str(llm.requests[2]["messages"])
    assert (
        "Baseline turn: 2; external wall-clock and budget limits govern"
        in second_round_prompt
    )
    assert "Baseline turn: 2/1" not in second_round_prompt
