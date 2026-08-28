from pathlib import Path
from types import SimpleNamespace

from baseline_controls.agent import create_agent
from baseline_controls.experiment import RUNS, load_run


ROOT = Path(__file__).resolve().parents[1]


def test_all_frozen_run_manifests_validate() -> None:
    loaded = {
        run_id: load_run(ROOT / "experiments/baseline-controls-2rep-v1/runs" / f"{run_id}.json")
        for run_id in RUNS
    }
    assert len(loaded) == 7
    assert {spec.condition for spec in loaded.values()} == {
        "qwen-stock-25", "gpt-stock-25", "portfolio-25x2", "qwen-stock-50", "gpt-stock-50"
    }


def test_solo_50_factory_changes_only_turn_ceiling(monkeypatch) -> None:
    monkeypatch.delenv("BASELINE_MODEL", raising=False)
    monkeypatch.delenv("BASELINE_MAX_TOKENS", raising=False)
    monkeypatch.delenv("BASELINE_TEMPERATURE", raising=False)
    agent = create_agent()
    assert agent.max_turns == 50
    assert agent.max_tokens == 12000
    assert agent.temperature == 0.2


def test_solo_50_final_attempt_moves_to_turn_50() -> None:
    agent = create_agent()
    problem = SimpleNamespace(id="p", description="d", challenge="theorem t : True := by trivial")
    assert "final attempt" not in agent._messages(problem, feedback="", turn=49, is_last=False)[0]["content"]
    assert "final attempt" in agent._messages(problem, feedback="", turn=50, is_last=True)[0]["content"]
