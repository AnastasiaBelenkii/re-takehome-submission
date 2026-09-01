from __future__ import annotations

import json

import pytest

from scripts.launch_online_microcell import result_summary, validate_api_key


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


def test_online_launch_requires_nonempty_api_key_without_exposing_it(tmp_path):
    with pytest.raises(RuntimeError, match="no readable"):
        validate_api_key(tmp_path)
    (tmp_path / ".env").write_text("UNRELATED=x\nOPENROUTER_API_KEY=\n")
    with pytest.raises(RuntimeError, match="no configured"):
        validate_api_key(tmp_path)
    (tmp_path / ".env").write_text("OPENROUTER_API_KEY=secret\n")
    validate_api_key(tmp_path)
