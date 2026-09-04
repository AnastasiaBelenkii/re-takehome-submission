from __future__ import annotations

import asyncio
import collections
import hashlib
import json
from pathlib import Path

import pytest

from collaboration_engine_v2.agent import CollaborationEngineV2Agent, TrackState
from collaboration_engine_v2.constants import CONDITIONS
from collaboration_engine_v2.experiment import build_queue, load_condition, load_resources
from collaboration_engine_v2.strategies import (
    NoCollaboration,
    PeerPacket,
    ReciprocalCadence,
    TrackObservation,
)
from collaboration_engine_v2.salvage import contains_sorry, propose_sorrifications
from collaboration_engine_v2.strategies import ProgressFillPackets, ProgressPackets
from collaboration_engine_v2.tactics import (
    canonicalize_imports,
    declarations_unchanged,
    imports_unchanged,
    required_declarations_present,
    tactic_candidate,
)
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
        self.requests_dispatched_by_model = collections.Counter()
        self.active = 0

    async def complete(self, **kwargs):
        self.requests.append(kwargs)
        self.requests_dispatched_by_model[kwargs["model"]] += 1
        self.active += 1
        try:
            value = self.responses[kwargs["model"]].pop(0)
            if isinstance(value, tuple):
                delay, value = value
                await asyncio.sleep(delay)
            if isinstance(value, BaseException): raise value
            return Response(value)
        finally:
            self.active -= 1


class Check:
    def __init__(self, accepted=False, message="bad", timed_out=False, messages=None, duration_ms=1):
        self.accepted, self.timed_out = accepted, timed_out
        self.duration_ms = duration_ms
        self.messages = messages if messages is not None else (
            [] if accepted else [{"severity": "error", "data": message}]
        )


class Lean:
    def __init__(self, outcomes): self.outcomes, self.sources = list(outcomes), []
    async def check_file(self, source, **_kwargs):
        self.sources.append(source)
        value = self.outcomes.pop(0)
        return Check(**value) if isinstance(value, dict) else Check(value)


class Services:
    def __init__(self, responses, outcomes, verifications=None):
        self.llm, self.lean, self.checkpoints = LLM(responses), Lean(outcomes), []
        self.verifications = list(verifications or [])
        self.verified_sources = []
    def checkpoint(self, source, metadata=None): self.checkpoints.append((source, metadata or {}))
    async def verify(self, source):
        self.verified_sources.append(source)
        passed = self.verifications.pop(0) if self.verifications else True
        if isinstance(passed, BaseException): raise passed
        return {
            "passed": passed, "answer_shape_passed": passed,
            "comparator_passed": passed, "comparator_timed_out": False,
            "comparator_exit_code": 0 if passed else 1,
        }


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


def test_sorrifier_preserves_prefix_and_later_declarations():
    candidate = """import Mathlib
theorem p : True := by
  have h : True := by
    trivial
  exact missing

lemma later : True := by trivial
"""
    messages = [{
        "severity": "error", "pos": {"line": 5, "column": 2},
        "endPos": {"line": 5, "column": 15},
        "data": "Unknown identifier `missing`\n⊢ True",
    }]
    proposals = propose_sorrifications(candidate, messages)
    assert len(proposals) == 3
    assert proposals[0].mode == "diagnostic_span"
    assert "have h : True" in proposals[0].source
    assert "exact missing" not in proposals[0].source
    assert "sorry" in proposals[0].source
    assert "lemma later : True := by trivial" in proposals[0].source
    assert contains_sorry(proposals[0].source)


def test_sorrifier_first_preserves_code_after_a_local_failure():
    candidate = """import Mathlib
theorem p : True := by
  have h : True := by
    exact missing
  exact h
"""
    messages = [{
        "severity": "error", "pos": {"line": 4, "column": 4},
        "endPos": {"line": 4, "column": 17}, "data": "Unknown identifier `missing`",
    }]
    proposals = propose_sorrifications(candidate, messages)
    assert proposals[0].mode == "diagnostic_span"
    assert "    sorry\n  exact h" in proposals[0].source
    assert proposals[0].retained_lines > 0


def test_sorrifier_fails_closed_on_statement_and_unpositioned_errors():
    candidate = "import Mathlib\ntheorem p : MissingType := by\n  trivial\n"
    statement_error = [{
        "severity": "error", "pos": {"line": 2, "column": 12},
        "data": "Unknown identifier `MissingType`",
    }]
    assert propose_sorrifications(candidate, statement_error) == ()
    assert propose_sorrifications(candidate, [{
        "severity": "error", "data": "malformed diagnostic without a position",
    }]) == ()


def test_sorrifier_does_not_count_comments_as_verified_progress():
    candidate = """import Mathlib
theorem p : True := by
  -- The library surely contains the exact result.
  -- Reuse it to finish immediately.
  exact Missing.exact_result
"""
    messages = [{
        "severity": "error", "pos": {"line": 5, "column": 8},
        "data": "Unknown constant `Missing.exact_result`",
    }]
    proposals = propose_sorrifications(candidate, messages)
    assert proposals
    assert all(proposal.retained_lines == 0 for proposal in proposals)


@pytest.mark.asyncio
async def test_zero_retention_sorrification_is_not_used_as_partial_state():
    broken = "import Mathlib\ntheorem p : True := by\n  exact missing\n"
    positioned_error = [{
        # The harness canonicalizes imports and inserts one blank line.
        "severity": "error", "pos": {"line": 4, "column": 2},
        "data": "Unknown identifier `missing`\n⊢ True",
    }]
    services = Services(
        {MODEL_A: [broken], MODEL_B: [source("b0")]},
        [False, {"messages": positioned_error}, False],
    )
    result = await agent(
        NoCollaboration(), max_calls_per_model=1, enable_salvage=True
    ).solve(problem(), services)

    events = result.metadata["tracks"][MODEL_A]["salvage_events"]
    assert events[-1]["reason"] == "no_retained_proof_structure"
    assert not contains_sorry(result.solution)
    assert all(not contains_sorry(value) for value, _metadata in services.checkpoints)


@pytest.mark.asyncio
async def test_c0plus_repairs_own_skeleton_and_c1plus_sends_progress_packet():
    broken = """import Mathlib
theorem p : True := by
  have h : True := by
    trivial
  exact missing
"""
    positioned_error = [{
        "severity": "error", "pos": {"line": 5, "column": 2},
        "data": "Unknown identifier `missing`\n⊢ True",
    }]
    sorry_warning = [{"severity": "warning", "data": "declaration uses `sorry`"}]

    async def run(strategy):
        services = Services(
            {MODEL_A: [broken, source("a1")], MODEL_B: [source("b0"), source("b1")]},
            [
                False,
                {"messages": positioned_error},
                {"messages": sorry_warning},
                False,
                False,
                False,
            ],
        )
        result = await agent(
            strategy, max_calls_per_model=2, enable_salvage=True
        ).solve(problem(), services)
        return services, result

    c0_services, c0_result = await run(NoCollaboration())
    c0_a2 = [r for r in c0_services.llm.requests if r["model"] == MODEL_A][1]
    assert "Warm-checked partial skeleton" in c0_a2["messages"][1]["content"]
    assert "sorry" in c0_a2["messages"][1]["content"]
    assert all("Compiler-grounded progress" not in r["messages"][1]["content"]
               for r in c0_services.llm.requests)
    assert c0_result.metadata["salvage_enabled"] is True

    c1_services, c1_result = await run(ProgressPackets(
        packet_chars=6000, models=(MODEL_A, MODEL_B)
    ))
    b_requests = [r for r in c1_services.llm.requests if r["model"] == MODEL_B]
    assert "Compiler-grounded progress" in b_requests[1]["messages"][1]["content"]
    assert "sorry" in b_requests[1]["messages"][1]["content"]
    events = c1_result.metadata["packet_events"]
    assert len(events) == 1
    assert events[0]["used_on_call"] == 2
    assert any(
        event.get("compiled") is True
        for event in c1_result.metadata["tracks"][MODEL_A]["salvage_events"]
    )
    assert not contains_sorry(c0_result.solution)
    assert not contains_sorry(c1_result.solution)
    assert all(not contains_sorry(value) for value, _metadata in c0_services.checkpoints)
    assert all(not contains_sorry(value) for value, _metadata in c1_services.checkpoints)


def test_progress_packet_queue_is_latest_wins_and_marks_stale_event():
    engine = agent(ProgressPackets(packet_chars=6000, models=(MODEL_A, MODEL_B)))
    tracks = {
        MODEL_A: TrackState(MODEL_A, problem().challenge),
        MODEL_B: TrackState(MODEL_B, problem().challenge),
    }
    events = []
    first = PeerPacket(MODEL_B, MODEL_A, "first progress", "progress-event-latest-v1")
    latest = PeerPacket(MODEL_B, MODEL_A, "latest progress", "progress-event-latest-v1")

    engine._install_packets((first,), tracks, 1, events, latest_wins=True)
    engine._install_packets((latest,), tracks, 2, events, latest_wins=True)

    assert len(tracks[MODEL_B].pending_packets) == 1
    assert tracks[MODEL_B].pending_packets[0][0] == latest
    assert events[0]["replaced_before_use"] is True
    assert "replaced_before_use" not in events[1]


@pytest.mark.asyncio
async def test_fast_track_reserve_waits_for_and_consumes_fill_packet():
    class PacketAfterSlowObservation:
        strategy_id = "progress-fill-event-latest-v2"

        def __init__(self):
            self.sent = False

        def after_round(self, _observations):
            return ()

        def after_observation(self, observation):
            if observation.model != MODEL_B or self.sent:
                return ()
            self.sent = True
            return (PeerPacket(
                MODEL_A, MODEL_B, "Compiling skeleton:\n" + problem().challenge,
                self.strategy_id,
            ),)

    responses = {
        MODEL_A: [source("a0"), (0.03, source("a1")), source("a2"), source("a3")],
        MODEL_B: [
            (0.02, source("b0")), (0.02, source("b1")),
            (0.02, source("b2")), (0.02, source("b3")),
        ],
    }
    services = Services(responses, [False] * 9)
    result = await agent(
        PacketAfterSlowObservation(), max_calls_per_model=4,
        fast_track_reserved_calls=1, dispatch_cutoff_s=10,
        reserve_release_margin_s=0.1,
    ).solve(problem(), services)

    qwen_requests = [
        request for request in services.llm.requests if request["model"] == MODEL_A
    ]
    assert len(qwen_requests) == 4
    fill_request = next(
        request for request in qwen_requests
        if "fill its residual holes now" in request["messages"][1]["content"]
    )
    fill_prompt = fill_request["messages"][1]["content"]
    fill_system = fill_request["messages"][0]["content"]
    assert "phase: peer_fill" in fill_prompt
    assert "fill its residual holes now" in fill_prompt
    assert "Do not critique" in fill_prompt
    assert "Critically evaluate" not in fill_prompt
    assert "Abandon the prior trajectory" not in fill_system
    event = result.metadata["packet_events"][0]
    assert event["used_on_call"] == 3
    assert event["delivery_delay_s"] >= 0
    assert result.metadata["tracks"][MODEL_A]["peer_packets_consumed"] == 1
    # Consuming an early packet does not permanently unlock the final reserve;
    # with no second packet, it releases only after the peer exhausts.
    dispatch_models = [request["model"] for request in services.llm.requests]
    assert max(index for index, model in enumerate(dispatch_models) if model == MODEL_A) > max(
        index for index, model in enumerate(dispatch_models) if model == MODEL_B
    )
    assert result.metadata["tracks"][MODEL_A]["reserve_release_reason"] == "peer_exhausted"


@pytest.mark.asyncio
async def test_idle_control_reserve_releases_only_after_peer_exhausts():
    responses = {
        MODEL_A: [source("a0"), source("a1"), source("a2")],
        MODEL_B: [(0.01, source("b0")), (0.01, source("b1")), (0.01, source("b2"))],
    }
    services = Services(responses, [False] * 7)
    result = await agent(
        NoCollaboration(), max_calls_per_model=3,
        fast_track_reserved_calls=1, dispatch_cutoff_s=10,
        reserve_release_margin_s=0.1,
    ).solve(problem(), services)

    dispatch_models = [request["model"] for request in services.llm.requests]
    assert max(index for index, model in enumerate(dispatch_models) if model == MODEL_A) > max(
        index for index, model in enumerate(dispatch_models) if model == MODEL_B
    )
    assert result.metadata["tracks"][MODEL_A]["reserve_release_reason"] == "peer_exhausted"


def test_tactic_substitution_preserves_every_pristine_declaration():
    manifest = json.loads((ROOT / "sample-problems/manifest.json").read_text())
    for item in manifest["problems"]:
        challenge = (ROOT / "sample-problems" / item["id"] / "challenge.lean").read_text()
        candidate = tactic_candidate(challenge)
        if ":= sorry" in challenge:
            assert candidate is None, item["id"]
            continue
        assert candidate is not None, item["id"]
        assert candidate != challenge
        assert declarations_unchanged(challenge, candidate), item["id"]


def test_contract_allows_fresh_helpers_but_not_required_declaration_changes():
    challenge = """import Mathlib
theorem p (n : ℕ) : n = n := by
  sorry
"""
    helper = """import Mathlib
lemma helper (n : ℕ) : n = n := by rfl
theorem p (n : ℕ) : n = n := by exact helper n
"""
    changed = helper.replace("theorem p (n : ℕ) : n = n", "theorem p (n : ℕ) : n + 0 = n")
    duplicate = helper + "\ntheorem p (n : ℕ) : n = n := by rfl\n"
    assert declarations_unchanged(challenge, helper)
    assert not declarations_unchanged(challenge, changed)
    assert not declarations_unchanged(challenge, duplicate)
    assert declarations_unchanged(
        challenge,
        helper.replace("lemma helper", "lemma p.helper"),
    )


def test_call_zero_never_substitutes_a_tactic_for_a_term_answer_hole():
    challenge = """import Mathlib
abbrev answer : ℕ := sorry
theorem p : answer = 49 := by sorry
"""
    assert tactic_candidate(challenge) is None


def test_live_structural_gate_ignores_semantic_source_spelling():
    challenge = """import Mathlib
theorem p (n : ℕ) (hn : 0 < n) : Finset.Icc 0 n = Finset.Icc 0 n := by sorry
"""
    equivalent_spelling = """import Mathlib
open Finset
theorem p (n : ℕ) (_ : 0 < n) : Icc 0 n = Icc 0 n := by rfl
"""
    changed_statement = equivalent_spelling.replace("Icc 0 n = Icc 0 n", "True")
    missing = "import Mathlib\nlemma helper : True := by trivial\n"
    duplicate = equivalent_spelling + equivalent_spelling
    assert required_declarations_present(challenge, equivalent_spelling)
    assert required_declarations_present(challenge, changed_statement)
    assert not required_declarations_present(challenge, missing)
    assert not required_declarations_present(challenge, duplicate)


def test_import_contract_requires_exact_pristine_imports():
    challenge = "import Mathlib.Order.Bounds.Basic\ntheorem p : True := by sorry\n"
    same = "import   Mathlib.Order.Bounds.Basic -- same module\ntheorem p : True := by trivial\n"
    broader = "import Mathlib\ntheorem p : True := by trivial\n"
    missing = "import Mathlib.This.Does.Not.Exist\ntheorem p : True := by trivial\n"
    assert imports_unchanged(challenge, same)
    assert not imports_unchanged(challenge, broader)
    assert not imports_unchanged(challenge, missing)
    normalized = canonicalize_imports(missing)
    assert normalized.startswith("import Mathlib\n\n")
    assert "Mathlib.This.Does.Not.Exist" not in normalized


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
        assert requests[0]["reasoning"] == {"effort": "medium"}
    assert [len(result.metadata["packet_events"]) for _s, result in arms] == [0, 2, 4]
    assert all(
        result.metadata["reasoning_effort_by_model"]
        == {MODEL_A: "medium", MODEL_B: "medium"}
        for _services, result in arms
    )


def test_reserve_arms_match_recorded_p07_first_request_bytes():
    """Guard Stage 5 seed-6211 request bytes while adding explicit track IDs."""
    problem_root = ROOT / "sample-problems/p07_least_divisible"
    recorded_problem = Problem(
        id="p07_least_divisible",
        description=(problem_root / "problem.md").read_text(),
        challenge=(problem_root / "challenge.lean").read_text(),
    )
    expected = {
        MODEL_A: "08ea22bc70705e8307f83a91ecfbc5acf5543c47d7a95d93bd69deb36499d626",
        MODEL_B: "43ec15c37174ee097881cbebd77004898f3039122cfb3f4c0841b3426b5d0139",
    }
    arms = (
        agent(
            NoCollaboration(), condition="c0plus-reserve", max_calls_per_model=25,
            seed=6211, enable_salvage=True, fast_track_reserved_calls=1,
        ),
        agent(
            ProgressFillPackets(packet_chars=6000, models=(MODEL_A, MODEL_B)),
            condition="c1plus-fill-reserve", max_calls_per_model=25, seed=6211,
            enable_salvage=True, fast_track_reserved_calls=1,
        ),
    )
    for model in (MODEL_A, MODEL_B):
        payloads = []
        for arm in arms:
            track = TrackState(
                model, recorded_problem.challenge, calls=1, seed=6211
            )
            request = {
                "model": model,
                "messages": arm._messages(recorded_problem, track, "direct", None),
                "max_tokens": arm.generation_max_tokens,
                "temperature": arm.temperature,
                "seed": track.seed,
                "reasoning": {"effort": "medium"},
            }
            payloads.append(json.dumps(
                request, sort_keys=True, separators=(",", ":")
            ).encode())
        assert payloads[0] == payloads[1]
        assert hashlib.sha256(payloads[0]).hexdigest() == expected[model]


@pytest.mark.asyncio
async def test_c0_qq_runs_and_logs_two_independent_qwen_tracks(monkeypatch):
    monkeypatch.setattr("collaboration_engine_v2.agent.tactic_candidate", lambda _source: None)
    qq = agent(
        NoCollaboration(), condition="c0-qq", models=(MODEL_A, MODEL_A),
        track_ids=("qwen#1", "qwen#2"), max_calls_per_model=1,
        seed=9201, enable_salvage=True, fast_track_reserved_calls=0,
    )
    services = Services(
        {MODEL_A: [source("qq1"), source("qq2")]},
        [True, True],
        verifications=[True],
    )

    result = await qq.solve(problem(), services)

    assert [request["model"] for request in services.llm.requests] == [MODEL_A, MODEL_A]
    assert [request["seed"] for request in services.llm.requests] == list(qq.track_seeds)
    assert len(set(qq.track_seeds)) == 2
    assert set(result.metadata["tracks"]) == {"qwen#1", "qwen#2"}
    assert all(
        track["model"] == MODEL_A and track["calls_dispatched"] == 1
        for track in result.metadata["tracks"].values()
    )
    completed = [
        event for event in result.metadata["verification_events"]
        if event["event"] == "completed"
    ]
    assert completed and completed[0]["passed"] is True


@pytest.mark.asyncio
@pytest.mark.parametrize("model", [MODEL_A, MODEL_B])
async def test_single_track_dispatches_only_its_model_without_peer_or_packets(model):
    solo_problem = Problem(
        id="answer",
        description="Return 1",
        challenge="import Mathlib\nabbrev answer : ℕ := sorry\n",
    )
    proposal = "import Mathlib\nabbrev answer : ℕ := 2\n"
    services = Services({model: [proposal]}, [False])

    result = await agent(
        NoCollaboration(),
        models=(model,),
        max_calls_per_model=1,
        enable_salvage=True,
        fast_track_reserved_calls=0,
    ).solve(solo_problem, services)

    assert [request["model"] for request in services.llm.requests] == [model]
    assert set(result.metadata["tracks"]) == {model}
    assert result.metadata["packet_events"] == []
    assert result.metadata["tracks"][model]["pending_peer_packets"] == 0


@pytest.mark.asyncio
async def test_fast_track_advances_without_waiting_and_packets_keep_provenance():
    responses = {
        MODEL_A: [(0.001, source(f"a{i}")) for i in range(3)],
        MODEL_B: [(0.05, source("b0")), (0.001, source("b1")), (0.001, source("b2"))],
    }
    services = Services(responses, [False] * 7)
    result = await agent(
        ReciprocalCadence(packet_chars=6000, repeat=True), max_calls_per_model=3
    ).solve(problem(), services)

    models_in_dispatch_order = [request["model"] for request in services.llm.requests]
    assert models_in_dispatch_order[:5] == [MODEL_A, MODEL_B, MODEL_A, MODEL_A, MODEL_B]
    a_requests = [r for r in services.llm.requests if r["model"] == MODEL_A]
    b_requests = [r for r in services.llm.requests if r["model"] == MODEL_B]
    assert all("Independent peer" not in r["messages"][1]["content"] for r in a_requests)
    assert "Independent peer" in b_requests[1]["messages"][1]["content"]
    assert "Independent peer" in b_requests[2]["messages"][1]["content"]

    events = result.metadata["packet_events"]
    b_events = [event for event in events if event["target_model"] == MODEL_B]
    a_events = [event for event in events if event["target_model"] == MODEL_A]
    assert [event.get("used_on_call") for event in b_events[:2]] == [2, 3]
    assert all("used_on_call" not in event for event in a_events)


@pytest.mark.asyncio
async def test_cancelling_agent_cancels_independent_inflight_requests():
    services = Services(
        {
            MODEL_A: [(60, source("a"))],
            MODEL_B: [(60, source("b"))],
        },
        [False],
    )
    task = asyncio.create_task(
        agent(NoCollaboration(), max_calls_per_model=1).solve(problem(), services)
    )
    while len(services.llm.requests) < 2:
        await asyncio.sleep(0)
    task.cancel()
    with pytest.raises(asyncio.CancelledError):
        await task
    await asyncio.sleep(0)
    assert services.llm.active == 0


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


@pytest.mark.asyncio
async def test_contract_rejection_is_transactional_and_never_checkpointed_or_packetized():
    invalid = "import Mathlib\nlemma helper : False := by trivial\n"
    responses = {
        MODEL_A: [invalid, source("a1")],
        MODEL_B: [source("b0"), source("b1")],
    }
    services = Services(responses, [False] * 4)
    result = await agent(
        ReciprocalCadence(packet_chars=6000, repeat=False), max_calls_per_model=2
    ).solve(problem(), services)

    # Call-zero and the three admissible proposals reach Lean; the rejected
    # proposal does not. It also cannot displace the call-zero checkpoint.
    assert invalid not in services.lean.sources
    assert all(checkpoint[0] != invalid for checkpoint in services.checkpoints)
    attempt = result.metadata["tracks"][MODEL_A]["attempts"][0]
    assert attempt["proposal_committed"] is False
    assert attempt["checkpoint_saved"] is False
    assert attempt["required_declarations_present"] is False

    # The next repair prompt shows the last admissible state (the pristine
    # challenge), while retaining a precise rejection diagnostic.
    second_a = [request for request in services.llm.requests if request["model"] == MODEL_A][1]
    prompt = second_a["messages"][1]["content"]
    assert "theorem p : True" in prompt
    assert "lemma helper : False" not in prompt
    assert "Candidate contract rejected before Lean" in prompt

    # C1's packet source is also the last admissible candidate, not the rejected
    # proposal. Condition cadence itself is unchanged.
    second_b = [request for request in services.llm.requests if request["model"] == MODEL_B][1]
    assert "lemma helper : False" not in second_b["messages"][1]["content"]


@pytest.mark.asyncio
async def test_warm_lean_success_is_provisional_until_fresh_verification_passes():
    warm_success = source("warm-only")
    services = Services(
        {MODEL_A: [warm_success], MODEL_B: [source("b0")]},
        [False, True, False],
        verifications=[False],
    )
    result = await agent(NoCollaboration(), max_calls_per_model=1).solve(problem(), services)
    attempt = result.metadata["tracks"][MODEL_A]["attempts"][0]
    assert attempt["lean_accepted"] is True
    assert attempt["compatibility_checked"] is True
    assert attempt["compatibility_passed"] is False
    assert attempt["accepted"] is False
    # A warm-valid proof is recoverable while the asynchronous fresh check is
    # running, but it is never marked accepted unless that check passes.
    assert attempt["checkpoint_saved"] is True
    assert services.checkpoints[-1][1]["compatibility_status"] == "provisional_warm_lean_passed"
    assert services.verified_sources == [canonicalize_imports(warm_success)]
    assert result.metadata["calls_dispatched"] == 2
    assert result.solution == canonicalize_imports(warm_success)


@pytest.mark.asyncio
async def test_freshly_verified_warm_success_can_stop_and_checkpoint():
    success = source("verified")
    services = Services(
        {MODEL_A: [success], MODEL_B: [source("b0")]},
        [False, True, False],
        verifications=[True],
    )
    result = await agent(NoCollaboration(), max_calls_per_model=1).solve(problem(), services)
    attempt = result.metadata["tracks"][MODEL_A]["attempts"][0]
    assert attempt["accepted"] is True
    assert attempt["compatibility_passed"] is True
    assert attempt["checkpoint_saved"] is True


@pytest.mark.asyncio
async def test_fresh_verification_does_not_block_independent_model_calls():
    release = asyncio.Event()

    class SlowVerificationServices(Services):
        async def verify(self, candidate):
            self.verified_sources.append(candidate)
            await release.wait()
            return {
                "passed": False, "answer_shape_passed": True,
                "comparator_passed": False, "comparator_timed_out": True,
                "comparator_exit_code": None,
            }

    services = SlowVerificationServices(
        {
            MODEL_A: [source("a0"), source("a1")],
            MODEL_B: [source("b0"), source("b1")],
        },
        [False, True, False, False, False],
    )
    task = asyncio.create_task(
        agent(NoCollaboration(), max_calls_per_model=2).solve(problem(), services)
    )
    while not services.verified_sources:
        await asyncio.sleep(0)
    for _ in range(100):
        if len(services.llm.requests) > 2:
            break
        await asyncio.sleep(0)
    assert len(services.llm.requests) > 2
    release.set()
    result = await task
    assert result.metadata["verification_policy"] == "single-flight-latest-v1"


@pytest.mark.asyncio
async def test_semantic_model_call_has_a_hard_wall_deadline():
    services = Services(
        {MODEL_A: [(60, source("a"))], MODEL_B: [(60, source("b"))]},
        [False],
    )
    result = await agent(
        NoCollaboration(), max_calls_per_model=1, model_call_wall_timeout_s=0.01
    ).solve(problem(), services)
    errors = [
        error for track in result.metadata["tracks"].values()
        for error in track["call_errors"]
    ]
    assert len(errors) == 2
    assert all(error["type"] == "TimeoutError" for error in errors)
    assert services.llm.active == 0


@pytest.mark.asyncio
async def test_helper_proposal_and_normalized_changed_import_reach_lean():
    helper = """import Mathlib
lemma helper : True := by trivial
theorem p : True := by exact helper
"""
    changed_import = "import Mathlib.This.Does.Not.Exist\ntheorem p : True := by trivial\n"
    services = Services(
        {MODEL_A: [helper], MODEL_B: [changed_import]},
        [False, False, False],
    )
    result = await agent(NoCollaboration(), max_calls_per_model=1).solve(problem(), services)
    assert canonicalize_imports(helper) in services.lean.sources
    assert changed_import not in services.lean.sources
    assert canonicalize_imports(changed_import) in services.lean.sources
    a_attempt = result.metadata["tracks"][MODEL_A]["attempts"][0]
    b_attempt = result.metadata["tracks"][MODEL_B]["attempts"][0]
    assert a_attempt["proposal_committed"] is True
    assert a_attempt["required_declarations_present"] is True
    assert b_attempt["proposal_committed"] is True
    assert b_attempt["original_imports_unchanged"] is False
    assert b_attempt["imports_normalized"] is True
