from __future__ import annotations

import json

from scripts.analyze_uplift_pilot import summarize_bundle
from uplift_pilot.experiment import EXPECTED_PROBLEMS


def _write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value))


def test_summary_derives_mechanisms_and_outer_timeout_from_raw_artifacts(tmp_path):
    bundle = tmp_path / "qwen-p-run"
    _write(bundle / "validation.json", {"valid": True})
    _write(
        bundle / "provenance.json",
        {"condition": "qwen-p", "model": "qwen/qwen3.5-flash-02-23", "policy": "P", "git_commit": "a" * 40},
    )
    run = bundle / "outputs" / "agent" / "timestamp"
    _write(run / "run.json", {})
    for index, problem_id in enumerate(EXPECTED_PROBLEMS):
        calls = []
        if index == 0:
            calls = [
                {
                    "request": {"messages": [{"content": "Produce a short structured strategy memo"}]},
                    "response": {"usage": {}, "choices": [{"message": {"content": None}}]},
                },
                {
                    "request": {"messages": [{"content": "Policy: P; phase: restart\nStrategy memo to follow:"}]},
                    "response": {"usage": {}, "choices": [{"message": {"content": "proof"}}]},
                },
            ]
        _write(
            run / problem_id / "result.json",
            {
                "passed": False,
                "status": "cost_unknown" if index == 0 else "failed",
                "wall_s": 1,
                "budget": {"spent_usd": 0},
                "comparator": {"timed_out": False},
                "agent_error": {"type": "TimeoutError"} if index == 0 else None,
                "agent_metadata": {},
            },
        )
        _write(run / problem_id / "transcript.json", {"calls": calls})

    summary = summarize_bundle(bundle)
    assert summary["planning_calls"] == 1
    assert summary["planning_memos_returned"] == 0
    assert summary["planning_memos_injected"] == 1
    assert summary["restarts"] == 1
    assert summary["agent_timeouts"] == 1
    assert summary["timeouts"] == 1
    assert summary["cost_unknown"] == 1
    assert summary["candidate_generation_calls"] == 1
