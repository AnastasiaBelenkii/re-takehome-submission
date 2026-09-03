from __future__ import annotations

import pytest

from re_harness import Problem
from re_harness.budget import BudgetAccountingError
from re_harness.models import MODEL_A
from uplift_pilot.agent import UpliftPilotAgent


class FakeResponse:
    def __init__(self, content):
        self.content = content


class FakeLLM:
    def __init__(self, responses):
        self.responses = list(responses)
        self.requests = []

    async def complete(self, **kwargs):
        self.requests.append(kwargs)
        response = self.responses.pop(0)
        if isinstance(response, BaseException):
            raise response
        return FakeResponse(response)


class FakeCheck:
    def __init__(self, accepted=False, messages=None, timed_out=False):
        self.accepted = accepted
        self.messages = messages if messages is not None else ([] if accepted else [{"severity": "error", "data": "bad"}])
        self.timed_out = timed_out


class FakeLean:
    def __init__(self, checks):
        self.checks = list(checks)
        self.sources = []

    async def check_file(self, source):
        self.sources.append(source)
        return self.checks.pop(0)


class FakeServices:
    def __init__(self, responses, checks):
        self.llm = FakeLLM(responses)
        self.lean = FakeLean(checks)
        self.checkpoints = []

    def checkpoint(self, source, metadata=None):
        self.checkpoints.append((source, metadata or {}))


def problem():
    return Problem(
        id="generic",
        description="Prove True.",
        challenge="import Mathlib\n\ntheorem generic : True := by\n  sorry\n",
    )


def source(label):
    return f"import Mathlib\n-- {label}\n"


@pytest.mark.asyncio
async def test_p_plans_once_after_first_failure_and_never_checks_memo():
    memo = "informal proof and Lean architecture"
    services = FakeServices(
        [source("direct"), memo, source("memo-conditioned success")],
        [FakeCheck(messages=[{"severity": "error", "data": "first failure"}]), FakeCheck(accepted=True)],
    )
    result = await UpliftPilotAgent(model=MODEL_A, policy="P", max_calls=5).solve(problem(), services)

    assert len(services.llm.requests) == 3
    assert services.llm.requests[1]["max_tokens"] == 2500
    assert "structured strategy memo" in services.llm.requests[1]["messages"][0]["content"]
    assert memo in services.llm.requests[2]["messages"][1]["content"]
    assert services.lean.sources == [source("direct"), source("memo-conditioned success")]
    assert result.metadata["planning_calls"] == 1
    assert result.metadata["restarts"] == 0


@pytest.mark.asyncio
async def test_p_retains_complete_token_bounded_planning_memo():
    memo = "plan-start\n" + ("subgoal detail\n" * 300) + "plan-tail-sentinel"
    services = FakeServices(
        [source("direct"), memo, source("memo-conditioned success")],
        [FakeCheck(), FakeCheck(accepted=True)],
    )
    await UpliftPilotAgent(model=MODEL_A, policy="P", max_calls=3).solve(problem(), services)
    generation_prompt = services.llm.requests[2]["messages"][1]["content"]
    assert "plan-start" in generation_prompt
    assert "plan-tail-sentinel" in generation_prompt


@pytest.mark.asyncio
async def test_p_call_ceiling_counts_planning_call():
    services = FakeServices([source("direct"), "memo", source("must not dispatch")], [FakeCheck()])
    result = await UpliftPilotAgent(model=MODEL_A, policy="P", max_calls=2).solve(problem(), services)
    assert len(services.llm.requests) == 2
    assert len(services.lean.sources) == 1
    assert result.metadata["calls_dispatched"] == 2


@pytest.mark.asyncio
async def test_d_exact_candidate_repetition_triggers_pristine_restart_with_memory():
    repeated = source("same")
    services = FakeServices(
        [repeated, repeated, source("diversified")],
        [FakeCheck(), FakeCheck(), FakeCheck(accepted=True)],
    )
    result = await UpliftPilotAgent(model=MODEL_A, policy="D", max_calls=3).solve(problem(), services)
    restart_prompt = services.llm.requests[2]["messages"][1]["content"]
    assert "phase: restart" in restart_prompt
    assert problem().challenge in restart_prompt
    assert "failed-approach memory" in restart_prompt
    assert "failed Lean candidate excerpt" in restart_prompt
    assert "-- same" in restart_prompt
    assert result.metadata["attempts"][1]["restart_reason"] == "repeated_normalized_candidate"
    assert result.metadata["planning_calls"] == 0


@pytest.mark.asyncio
async def test_d_requires_two_unchanged_error_transitions():
    error = [{"severity": "error", "data": "same normalized error"}]
    services = FakeServices(
        [source("one"), source("two"), source("three"), source("restart")],
        [FakeCheck(messages=error), FakeCheck(messages=error), FakeCheck(messages=error), FakeCheck(accepted=True)],
    )
    result = await UpliftPilotAgent(model=MODEL_A, policy="D", max_calls=4).solve(problem(), services)
    phases = [request["messages"][1]["content"].split("phase: ", 1)[1].split("\n", 1)[0] for request in services.llm.requests]
    assert phases == ["direct", "repair", "repair", "restart"]
    assert result.metadata["attempts"][2]["restart_reason"] == "unchanged_error_signature_two_transitions"


@pytest.mark.asyncio
async def test_d_caps_restarts_at_two_and_enforces_calls():
    repeated = source("same")
    services = FakeServices([repeated] * 6, [FakeCheck()] * 6)
    result = await UpliftPilotAgent(model=MODEL_A, policy="D", max_calls=6).solve(problem(), services)
    assert result.metadata["restarts"] == 2
    assert result.metadata["calls_dispatched"] == 6
    assert len(services.llm.requests) == 6
    assert all(request["max_tokens"] == 12000 for request in services.llm.requests)


@pytest.mark.asyncio
async def test_best_checkpoint_and_return_value_survive_regression():
    better, worse = source("better"), source("worse")
    services = FakeServices(
        [better, worse],
        [
            FakeCheck(messages=[{"severity": "error", "data": "one"}]),
            FakeCheck(messages=[{"severity": "error", "data": "one"}, {"severity": "error", "data": "two"}]),
        ],
    )
    result = await UpliftPilotAgent(model=MODEL_A, policy="D", max_calls=2).solve(problem(), services)
    assert result.solution == better
    assert [candidate for candidate, _ in services.checkpoints] == [better]


@pytest.mark.asyncio
async def test_predispatch_budget_refusal_does_not_inflate_call_ledger():
    services = FakeServices([source("first"), BudgetAccountingError("ledger closed")], [FakeCheck()])
    result = await UpliftPilotAgent(model=MODEL_A, policy="D", max_calls=25).solve(problem(), services)
    assert len(services.llm.requests) == 2
    assert result.metadata["calls_dispatched"] == 1
    assert result.metadata["call_errors"][-1]["dispatched"] is False
