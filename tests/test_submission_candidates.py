from __future__ import annotations

import pytest

from collaboration_engine_v2.agent import CollaborationEngineV2Agent
from re_harness.models import MODEL_A, MODEL_B
from submission.agent import create_agent as create_submission_agent
from submission.candidates import CANDIDATE_FACTORIES


@pytest.mark.parametrize(
    ("condition", "strategy", "salvage", "reserve"),
    [
        ("c0", "none", False, 0),
        ("c1", "reciprocal-once-v1", False, 0),
        ("c2", "reciprocal-every-eligible-v1", False, 0),
        ("c0plus-reserve", "none", True, 1),
        ("c1plus-fill-reserve", "progress-fill-event-latest-v2", True, 1),
        ("qwen-solo-plus", "none", True, 0),
        ("gptoss-solo-plus", "none", True, 0),
    ],
)
def test_candidate_factory_has_judge_defaults(
    monkeypatch, condition, strategy, salvage, reserve
):
    for name in (
        "COLLAB_CONDITION", "COLLAB_STRATEGY", "COLLAB_MAX_CALLS_PER_MODEL",
        "COLLAB_DISPATCH_CUTOFF_S", "COLLAB_ENABLE_SALVAGE",
        "COLLAB_FAST_TRACK_RESERVED_CALLS",
    ):
        monkeypatch.delenv(name, raising=False)
    monkeypatch.setenv("VM_TIME_LIMIT_S", "28800")

    agent = CANDIDATE_FACTORIES[condition]()

    assert agent.condition == condition
    assert agent.strategy.strategy_id == strategy
    assert agent.enable_salvage is salvage
    assert agent.fast_track_reserved_calls == reserve
    assert agent.max_calls_per_model is None
    assert agent.dispatch_cutoff_s == 28080


@pytest.mark.parametrize(
    ("condition", "model"),
    [("qwen-solo-plus", MODEL_A), ("gptoss-solo-plus", MODEL_B)],
)
def test_solo_candidate_has_exactly_one_model_and_no_packet_path(condition, model):
    agent = CANDIDATE_FACTORIES[condition]()

    assert agent.models == (model,)
    assert agent.strategy.strategy_id == "none"
    assert agent.enable_salvage is True
    assert agent.fast_track_reserved_calls == 0


def test_candidate_cutoff_tracks_evaluator_time_limit(monkeypatch):
    monkeypatch.setenv("VM_TIME_LIMIT_S", "1800")
    monkeypatch.delenv("COLLAB_DISPATCH_CUTOFF_S", raising=False)
    assert CANDIDATE_FACTORIES["c2"]().dispatch_cutoff_s == 1080


def test_default_submission_promotes_c1plus_fill_reserve(monkeypatch):
    monkeypatch.setenv("VM_TIME_LIMIT_S", "28800")
    monkeypatch.delenv("COLLAB_DISPATCH_CUTOFF_S", raising=False)

    agent = create_submission_agent()

    assert isinstance(agent, CollaborationEngineV2Agent)
    assert agent.condition == "c1plus-fill-reserve"
    assert agent.strategy.strategy_id == "progress-fill-event-latest-v2"
    assert agent.enable_salvage is True
    assert agent.fast_track_reserved_calls == 1
    assert agent.dispatch_cutoff_s == 28080
