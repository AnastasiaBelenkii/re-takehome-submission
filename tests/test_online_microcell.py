from __future__ import annotations

import json

import pytest

from scripts.launch_online_microcell import (
    preliminary_summary,
    result_summary,
    validate_api_key,
)


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


def test_preliminary_summary_ignores_provisional_then_reports_final_checkpoint(tmp_path):
    output = tmp_path / "outputs"
    checkpoint = output / "agent" / "timestamp" / "problem" / "checkpoint.json"
    checkpoint.parent.mkdir(parents=True)
    checkpoint.write_text(json.dumps({"metadata": {
        "phase": "deterministic_call_zero",
        "compatibility_status": "provisional_lean_failure",
    }}))
    assert preliminary_summary(output, tmp_path) is None

    checkpoint.write_text(json.dumps({"metadata": {
        "scheduler": "independent-track-v1",
        "calls_attempted": 5,
        "calls_dispatched": 5,
        "physical_requests": 5,
        "dispatch_cutoff_reached": True,
        "deterministic": {"lean_accepted": False, "accepted": False},
        "packet_events": [
            {"after_round": 1, "used_on_call": 2},
            {"after_round": 1},
        ],
        "tracks": {
            "fast": {
                "pending_peer_packets": 1,
                "attempts": [
                    {"required_declarations_present": True, "lean_accepted": False},
                    {"required_declarations_present": False, "lean_accepted": False},
                ],
            },
            "slow": {
                "pending_peer_packets": 0,
                "attempts": [
                    {
                        "required_declarations_present": True,
                        "lean_accepted": True,
                        "accepted": True,
                    }
                ],
            },
        },
    }}))

    assert preliminary_summary(output, tmp_path) == {
        "schema_version": 1,
        "status": "preliminary_agent_complete",
        "final_judging_pending": True,
        "checkpoint_path": "outputs/agent/timestamp/problem/checkpoint.json",
        "scheduler": "independent-track-v1",
        "calls_attempted": 5,
        "calls_dispatched": 5,
        "physical_requests": 5,
        "dispatch_cutoff_reached": True,
        "structural_rejections": 1,
        "warm_lean_successes": 1,
        "fresh_verified_successes": 1,
        "packets_generated": 2,
        "packets_used": 1,
        "packets_pending": 1,
    }
