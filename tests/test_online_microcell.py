from __future__ import annotations

import json

from scripts.launch_online_microcell import result_summary


def test_microcell_status_classifies_scientific_result_not_only_process_exit(tmp_path):
    output = tmp_path / "outputs"
    result = output / "agent" / "timestamp" / "problem" / "result.json"
    result.parent.mkdir(parents=True)
    result.write_text(json.dumps({
        "status": "harness_error",
        "passed": False,
        "agent_metadata": {"calls_dispatched": 0},
    }))

    assert result_summary(output, tmp_path) == {
        "result_artifact_count": 1,
        "result_path": "outputs/agent/timestamp/problem/result.json",
        "result_status": "harness_error",
        "result_passed": False,
        "result_calls_dispatched": 0,
    }


def test_microcell_status_refuses_ambiguous_results(tmp_path):
    output = tmp_path / "outputs"
    for name in ("one", "two"):
        result = output / name / "result.json"
        result.parent.mkdir(parents=True)
        result.write_text("{}")

    assert result_summary(output, tmp_path) == {
        "result_artifact_count": 2,
        "result_status": "missing_or_ambiguous",
    }
