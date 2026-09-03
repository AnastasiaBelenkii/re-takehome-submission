from __future__ import annotations

import asyncio
import json

import pytest

from collaboration_engine.agent import CollaborationEngineAgent
from collaboration_engine.experiment import load_condition
from collaboration_engine.strategies import NoCollaboration, PeerPacket, ReciprocalCrossRepair
from re_harness import Problem
from re_harness.models import MODEL_A, MODEL_B


class Response:
    def __init__(self, content):
        self.content = content


class LLM:
    def __init__(self, responses):
        self.responses = {model: list(values) for model, values in responses.items()}
        self.requests = []
        self.in_flight = 0
        self.max_in_flight = 0

    async def complete(self, **kwargs):
        self.requests.append(kwargs)
        self.in_flight += 1
        self.max_in_flight = max(self.max_in_flight, self.in_flight)
        await asyncio.sleep(0)
        self.in_flight -= 1
        value = self.responses[kwargs["model"]].pop(0)
        if isinstance(value, BaseException):
            raise value
        return Response(value)


class Check:
    def __init__(self, accepted=False, message="bad"):
        self.accepted = accepted
        self.timed_out = False
        self.messages = [] if accepted else [{"severity": "error", "data": message}]


class Lean:
    def __init__(self, outcomes):
        self.outcomes = outcomes
        self.sources = []

    async def check_file(self, source):
        self.sources.append(source)
        outcome = self.outcomes[source]
        return Check(*outcome) if isinstance(outcome, tuple) else Check(outcome)


class Services:
    def __init__(self, responses, outcomes):
        self.llm = LLM(responses)
        self.lean = Lean(outcomes)
        self.checkpoints = []

    def checkpoint(self, source, metadata=None):
        self.checkpoints.append((source, metadata or {}))


def problem():
    return Problem(id="p", description="Prove True", challenge="import Mathlib\ntheorem p : True := by\n  sorry\n")


def source(label):
    return f"import Mathlib\n-- {label}\n"


async def run(strategy):
    values = {
        MODEL_A: [source("a0"), source("a1")],
        MODEL_B: [source("b0"), source("b1")],
    }
    outcomes = {value: False for group in values.values() for value in group}
    services = Services(values, outcomes)
    result = await CollaborationEngineAgent(strategy=strategy, max_calls_per_model=2).solve(problem(), services)
    return services, result


@pytest.mark.asyncio
async def test_first_round_is_byte_identical_and_only_peer_packets_change_round_two():
    none_services, none_result = await run(NoCollaboration())
    collab_services, collab_result = await run(ReciprocalCrossRepair(packet_chars=6000))
    for model in (MODEL_A, MODEL_B):
        none_requests = [item for item in none_services.llm.requests if item["model"] == model]
        collab_requests = [item for item in collab_services.llm.requests if item["model"] == model]
        assert none_requests[0] == collab_requests[0]
        assert none_requests[1]["messages"][0] == collab_requests[1]["messages"][0]
        assert collab_requests[1]["messages"][1]["content"].startswith(
            none_requests[1]["messages"][1]["content"]
        )
        assert "Evidence from an independent solver" not in str(none_requests[1]["messages"])
        assert "Evidence from an independent solver" in str(collab_requests[1]["messages"])
    assert none_result.metadata["calls_dispatched"] == collab_result.metadata["calls_dispatched"] == 4
    assert none_services.llm.max_in_flight == collab_services.llm.max_in_flight == 2
    assert len(collab_result.metadata["packet_events"]) == 2


@pytest.mark.asyncio
async def test_empty_strategy_is_trace_equivalent_to_none():
    class Empty:
        strategy_id = "empty-test"
        def after_round(self, observations):
            return ()

    left, left_result = await run(NoCollaboration())
    right, right_result = await run(Empty())
    assert left.llm.requests == right.llm.requests
    assert left.lean.sources == right.lean.sources
    assert left_result.solution == right_result.solution


@pytest.mark.asyncio
async def test_strategy_cannot_inject_self_unknown_or_oversize_packets():
    class Invalid:
        strategy_id = "invalid"
        def __init__(self, packet): self.packet = packet
        def after_round(self, observations): return (self.packet,)

    bad_packets = [
        PeerPacket(MODEL_A, MODEL_A, "x", "bad"),
        PeerPacket("unknown", MODEL_A, "x", "bad"),
        PeerPacket(MODEL_A, MODEL_B, "x" * 11, "bad"),
    ]
    for packet in bad_packets:
        values = {MODEL_A: [source("a")], MODEL_B: [source("b")]}
        services = Services(values, {source("a"): False, source("b"): False})
        with pytest.raises(ValueError):
            await CollaborationEngineAgent(strategy=Invalid(packet), max_calls_per_model=1, peer_packet_chars=10).solve(problem(), services)


@pytest.mark.asyncio
async def test_global_best_checkpoint_survives_later_regression():
    a0, b0 = source("a0"), source("b0")
    services = Services(
        {MODEL_A: [a0], MODEL_B: [b0]},
        {a0: (False, "one"), b0: (False, "two errors collapsed")},
    )
    result = await CollaborationEngineAgent(strategy=NoCollaboration(), max_calls_per_model=1).solve(problem(), services)
    assert result.solution == a0
    assert [item[0] for item in services.checkpoints] == [a0]


def test_frozen_manifests_share_exact_resources_and_only_treatment_varies():
    root = __import__("pathlib").Path(__file__).parents[1]
    left_path = root / "experiments/collaboration-engine-v1/conditions/hd-none.json"
    right_path = root / "experiments/collaboration-engine-v1/conditions/hd-reciprocal.json"
    left, right = load_condition(left_path), load_condition(right_path)
    assert left.resources == right.resources
    raw_left, raw_right = json.loads(left_path.read_text()), json.loads(right_path.read_text())
    for key in ("condition", "collaboration_strategy"):
        raw_left.pop(key); raw_right.pop(key)
    assert raw_left == raw_right


def test_prompts_do_not_expose_condition_strategy_or_hashes():
    agent = CollaborationEngineAgent(strategy=NoCollaboration(), condition="secret-condition", max_calls_per_model=1)
    from collaboration_engine.agent import TrackState
    text = str(agent._messages(problem(), TrackState(MODEL_A, problem().challenge, calls=1), "direct", None))
    assert "secret-condition" not in text
    assert "none" not in text
    assert "sha256" not in text.lower()


@pytest.mark.asyncio
async def test_generic_call_error_does_not_change_other_track_or_call_accounting():
    a1, b0, b1 = (source(label) for label in ("a1", "b0", "b1"))
    services = Services(
        {MODEL_A: [RuntimeError("temporary"), a1], MODEL_B: [b0, b1]},
        {a1: False, b0: False, b1: False},
    )
    result = await CollaborationEngineAgent(strategy=NoCollaboration(), max_calls_per_model=2).solve(problem(), services)
    assert result.metadata["calls_dispatched"] == 4
    assert result.metadata["tracks"][MODEL_A]["call_errors"][0]["dispatched"] is True
    assert services.lean.sources == [b0, a1, b1]
