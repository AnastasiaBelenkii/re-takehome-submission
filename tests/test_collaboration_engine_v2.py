from __future__ import annotations

import asyncio
import json
from pathlib import Path

import pytest

from collaboration_engine_v2.agent import CollaborationEngineV2Agent
from collaboration_engine_v2.constants import CONDITIONS
from collaboration_engine_v2.experiment import build_queue, load_condition, load_resources
from collaboration_engine_v2.strategies import NoCollaboration, ReciprocalCadence, TrackObservation
from collaboration_engine_v2.tactics import declarations_unchanged, tactic_candidate
from re_harness import Problem
from re_harness.llm import CostFreeRateLimitError, LLMCallError
from re_harness.models import MODEL_A, MODEL_B

ROOT = Path(__file__).parents[1]


class Response:
    def __init__(self, content): self.content = content


class LLM:
    def __init__(self, responses):
        self.responses = {model: list(values) for model, values in responses.items()}
        self.requests = []

    async def complete(self, **kwargs):
        self.requests.append(kwargs)
        value = self.responses[kwargs["model"]].pop(0)
        if isinstance(value, BaseException): raise value
        return Response(value)


class Check:
    def __init__(self, accepted=False, message="bad", timed_out=False):
        self.accepted, self.timed_out = accepted, timed_out
        self.messages = [] if accepted else [{"severity": "error", "data": message}]


class Lean:
    def __init__(self, outcomes): self.outcomes, self.sources = list(outcomes), []
    async def check_file(self, source):
        self.sources.append(source)
        value = self.outcomes.pop(0)
        return Check(**value) if isinstance(value, dict) else Check(value)


class Services:
    def __init__(self, responses, outcomes):
        self.llm, self.lean, self.checkpoints = LLM(responses), Lean(outcomes), []
    def checkpoint(self, source, metadata=None): self.checkpoints.append((source, metadata or {}))


def problem():
    return Problem(id="p", description="Prove True",
                   challenge="import Mathlib\ntheorem p : True := by\n  sorry\n")


def source(label):
    return f"import Mathlib\n-- {label}\ntheorem p : True := by\n  trivial\n"


def agent(strategy, **kwargs):
    return CollaborationEngineV2Agent(
        strategy=strategy, max_calls_per_model=kwargs.pop("max_calls_per_model", 2),
        retry_backoff_s=0, **kwargs,
    )


def test_tactic_substitution_preserves_every_pristine_declaration():
    manifest = json.loads((ROOT / "sample-problems/manifest.json").read_text())
    for item in manifest["problems"]:
        challenge = (ROOT / "sample-problems" / item["id"] / "challenge.lean").read_text()
        candidate = tactic_candidate(challenge)
        assert candidate is not None, item["id"]
        assert candidate != challenge
        assert declarations_unchanged(challenge, candidate), item["id"]


def test_manifests_only_vary_condition_and_strategy_and_queue_is_frozen():
    paths = [ROOT / f"experiments/collaboration-engine-v2/conditions/{name}.json" for name in CONDITIONS]
    raw = [json.loads(path.read_text()) for path in paths]
    stripped = []
    for value in raw:
        stripped.append({key: item for key, item in value.items()
                         if key not in {"condition", "collaboration_strategy"}})
    assert stripped[0] == stripped[1] == stripped[2]
    conditions = {path.stem: load_condition(path) for path in paths}
    assert len(build_queue(conditions)) == 87
    resources = load_resources(ROOT / "experiments/collaboration-engine-v2/resources.json")
    assert resources["shallow"]["outer_time_s"] == 28 * 60
    assert resources["deep"]["outer_time_s"] == 8 * 60 * 60


@pytest.mark.asyncio
async def test_successful_tactic_is_call_zero_and_checkpointed():
    services = Services({MODEL_A: [], MODEL_B: []}, [True])
    result = await agent(NoCollaboration()).solve(problem(), services)
    assert result.metadata["deterministic"]["accepted"] is True
    assert result.metadata["calls_dispatched"] == result.metadata["physical_requests"] == 0
    assert len(services.checkpoints) == 1


async def run_arm(strategy):
    responses = {MODEL_A: [source("a0"), source("a1")], MODEL_B: [source("b0"), source("b1")]}
    services = Services(responses, [False] * 5)
    result = await agent(strategy).solve(problem(), services)
    return services, result


@pytest.mark.asyncio
async def test_c0_c1_c2_first_round_requests_are_byte_identical_for_paired_seed():
    arms = [await run_arm(NoCollaboration()),
            await run_arm(ReciprocalCadence(packet_chars=6000, repeat=False)),
            await run_arm(ReciprocalCadence(packet_chars=6000, repeat=True))]
    for model in (MODEL_A, MODEL_B):
        requests = [[r for r in services.llm.requests if r["model"] == model][0]
                    for services, _result in arms]
        assert requests[0] == requests[1] == requests[2]
        assert requests[0]["seed"] == 1
    assert [len(result.metadata["packet_events"]) for _s, result in arms] == [0, 2, 4]


@pytest.mark.asyncio
async def test_only_explicit_cost_free_429_retries_same_semantic_request():
    retry = CostFreeRateLimitError("free")
    services = Services({MODEL_A: [retry, source("a")], MODEL_B: [source("b")]}, [False] * 3)
    result = await agent(NoCollaboration(), max_calls_per_model=1).solve(problem(), services)
    assert result.metadata["calls_dispatched"] == 2
    assert result.metadata["physical_requests"] == 3
    assert result.metadata["cost_free_429_retries"] == 1
    a_requests = [r for r in services.llm.requests if r["model"] == MODEL_A]
    assert a_requests[0] == a_requests[1]


@pytest.mark.asyncio
async def test_uncertain_spend_error_is_not_retried():
    services = Services({MODEL_A: [LLMCallError("spend uncertain")], MODEL_B: [source("b")]}, [False, False])
    result = await agent(NoCollaboration(), max_calls_per_model=1).solve(problem(), services)
    assert len([r for r in services.llm.requests if r["model"] == MODEL_A]) == 1
    assert result.metadata["cost_free_429_retries"] == 0


def observation(model, round_number, *, accepted=False, timed_out=False):
    return TrackObservation(model, round_number, round_number, source(model), "bad", accepted, timed_out)


def test_cadence_handles_partial_errors_timeouts_and_acceptance():
    c1 = ReciprocalCadence(packet_chars=1000, repeat=False)
    assert c1.after_round([observation(MODEL_A, 1)]) == ()
    assert len(c1.after_round([observation(MODEL_A, 2, timed_out=True), observation(MODEL_B, 2)])) == 2
    assert c1.after_round([observation(MODEL_A, 3), observation(MODEL_B, 3)]) == ()
    c2 = ReciprocalCadence(packet_chars=1000, repeat=True)
    assert c2.after_round([observation(MODEL_A, 1), observation(MODEL_B, 1, accepted=True)]) == ()
    assert len(c2.after_round([observation(MODEL_A, 2), observation(MODEL_B, 2)])) == 2
    assert len(c2.after_round([observation(MODEL_A, 3), observation(MODEL_B, 3, timed_out=True)])) == 2


@pytest.mark.asyncio
async def test_cutoff_starts_no_round_and_retains_deterministic_checkpoint():
    ticks = iter([0.0, 100.0])
    services = Services({MODEL_A: [], MODEL_B: []}, [False])
    result = await agent(NoCollaboration(), clock=lambda: next(ticks), dispatch_cutoff_s=10).solve(problem(), services)
    assert result.metadata["dispatch_cutoff_reached"] is True
    assert result.metadata["calls_dispatched"] == 0
    assert services.checkpoints


@pytest.mark.asyncio
async def test_restart_prompt_requires_sketch_and_checkpoint_survives_regression():
    repeated = source("same")
    services = Services({MODEL_A: [repeated] * 4, MODEL_B: [source(f"b{i}") for i in range(4)]}, [False] * 9)
    result = await agent(NoCollaboration(), max_calls_per_model=4).solve(problem(), services)
    assert result.metadata["tracks"][MODEL_A]["restarts"] >= 1
    restart = next(r for r in services.llm.requests
                   if r["model"] == MODEL_A and "phase: restart" in r["messages"][1]["content"])
    assert "3-8 line proof sketch" in restart["messages"][0]["content"]
    assert services.checkpoints

