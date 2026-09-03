from __future__ import annotations

import json
import shutil
from pathlib import Path

import pytest

from uplift_pilot.experiment import EXPECTED_PROBLEMS, load_condition, sha256_file
from uplift_pilot.validation import validate_bundle, write_validation_artifacts


ROOT = Path(__file__).resolve().parents[1]
CONDITION_PATH = ROOT / "experiments/uplift-pilot-v1/conditions/qwen-p.json"
COMMIT = "a" * 40


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


def make_bundle(tmp_path):
    bundle = tmp_path / f"qwen-p-20260827T000000.000000Z-{COMMIT[:8]}"
    bundle.mkdir()
    condition = load_condition(CONDITION_PATH)
    shutil.copyfile(CONDITION_PATH, bundle / "condition.json")
    (bundle / "run.log").write_text("completed\n")
    (bundle / "run.pid").write_text("123\n")
    run_dir = bundle / "outputs/uplift_agent/20260827T000000Z"
    effective = condition.effective_configuration(
        problems_path=Path("/frozen/.uplift-runtime/problem-set"),
        output_root=bundle / "outputs",
    )
    provenance = {
        "schema_version": 1,
        "experiment": "uplift-pilot-v1",
        "design_id": "uplift-pilot-v1",
        "condition": "qwen-p",
        "model": condition.model,
        "policy": "P",
        "launched_at": "20260827T000000.000000Z",
        "git_commit": COMMIT,
        "manifest_sha256": condition.manifest_sha256,
        "problem_list_sha256": sha256_file(CONDITION_PATH.parent.parent / "problems.txt"),
        "launcher_sha256": sha256_file(ROOT / "scripts/launch_uplift_pilot.py"),
        "lean_image": condition.resources["lean_image"],
        "command": ["python", "run.py", "--agent", effective["agent"]],
        "effective_configuration": effective,
        "host": {"hostname": "worker"},
    }
    write_json(bundle / "provenance.json", provenance)
    finished = "2026-08-27T00:01:00+00:00"
    write_json(
        run_dir / "run.json",
        {"run_id": "run-1", "finished_at": finished, "agent": effective["agent"]},
    )
    summary_rows = []
    for problem_id in EXPECTED_PROBLEMS:
        problem_dir = run_dir / problem_id
        request = {
            "schema_version": 1,
            "seq": 1,
            "event": "llm_request",
            "call_id": f"{problem_id}-1",
            "request": {"model": condition.model, "messages": []},
        }
        response = {
            "schema_version": 1,
            "seq": 2,
            "event": "llm_response",
            "call_id": f"{problem_id}-1",
            "actual_cost_usd": 0.01,
        }
        problem_dir.mkdir(parents=True)
        (problem_dir / "events.jsonl").write_text(json.dumps(request) + "\n" + json.dumps(response) + "\n")
        (problem_dir / "solution.lean").write_text("import Mathlib\n")
        write_json(
            problem_dir / "transcript.json",
            {"problem_id": problem_id, "calls": [{"call_id": f"{problem_id}-1"}], "actual_cost_usd": 0.01},
        )
        write_json(
            problem_dir / "result.json",
            {
                "problem_id": problem_id,
                "status": "failed",
                "passed": False,
                "budget": {"spent_usd": 0.01, "accounting_complete": True},
                "models_used": [condition.model],
                "agent_metadata": {
                    "design_id": "uplift-pilot-v1",
                    "condition": "qwen-p",
                    "model": condition.model,
                    "calls_dispatched": 1,
                },
            },
        )
        summary_rows.append(
            {"problem_id": problem_id, "status": "failed", "passed": False, "actual_cost_usd": 0.01}
        )
    write_json(
        run_dir / "summary.json",
        {
            "finished_at": finished,
            "problems": summary_rows,
            "total_points": 0,
            "actual_cost_usd": 0.06,
        },
    )
    return bundle, run_dir


def test_valid_bundle_emits_report_and_checksums(tmp_path):
    bundle, _ = make_bundle(tmp_path)
    validation = validate_bundle(bundle, expected_condition_path=CONDITION_PATH, expected_commit=COMMIT)
    assert validation.valid, validation.errors
    assert len(validation.report["problems"]) == 6
    write_validation_artifacts(bundle, validation)
    assert (bundle / "validation.json").is_file()
    assert (bundle / "validation.txt").read_text().startswith("VALID")
    assert "provenance.json" in (bundle / "checksums.sha256").read_text()


@pytest.mark.parametrize(
    ("mutation", "expected"),
    [
        ("missing_problem", "unreadable JSON"),
        ("wrong_model", "model does not match"),
        ("wrong_commit", "git_commit mismatch"),
        ("mismatched_limits", "effective configuration"),
        ("excess_calls", "exceed ceiling"),
        ("unfinished", "finished_at"),
        ("leaked_secret", "apparent API key"),
    ],
)
def test_validator_detects_required_failures(tmp_path, mutation, expected):
    bundle, run_dir = make_bundle(tmp_path)
    first = run_dir / EXPECTED_PROBLEMS[0]
    if mutation == "missing_problem":
        (first / "result.json").unlink()
    elif mutation == "wrong_model":
        events = [json.loads(line) for line in (first / "events.jsonl").read_text().splitlines()]
        events[0]["request"]["model"] = "openai/gpt-oss-120b"
        (first / "events.jsonl").write_text("".join(json.dumps(event) + "\n" for event in events))
        result = json.loads((first / "result.json").read_text())
        result["models_used"] = ["openai/gpt-oss-120b"]
        write_json(first / "result.json", result)
    elif mutation == "wrong_commit":
        provenance = json.loads((bundle / "provenance.json").read_text())
        provenance["git_commit"] = "b" * 40
        write_json(bundle / "provenance.json", provenance)
    elif mutation == "mismatched_limits":
        provenance = json.loads((bundle / "provenance.json").read_text())
        provenance["effective_configuration"]["environment"]["UPLIFT_MAX_CALLS"] = "24"
        write_json(bundle / "provenance.json", provenance)
    elif mutation == "excess_calls":
        condition = load_condition(CONDITION_PATH)
        requests = []
        calls = []
        for index in range(26):
            call_id = f"call-{index}"
            requests.append(json.dumps({"event": "llm_request", "call_id": call_id, "request": {"model": condition.model}}) + "\n")
            calls.append({"call_id": call_id})
        (first / "events.jsonl").write_text("".join(requests))
        transcript = json.loads((first / "transcript.json").read_text())
        transcript["calls"] = calls
        write_json(first / "transcript.json", transcript)
        result = json.loads((first / "result.json").read_text())
        result["agent_metadata"]["calls_dispatched"] = 26
        write_json(first / "result.json", result)
    elif mutation == "unfinished":
        run = json.loads((run_dir / "run.json").read_text())
        run["finished_at"] = None
        write_json(run_dir / "run.json", run)
    elif mutation == "leaked_secret":
        fake_key = "sk-or-v1-" + "test-only-not-a-real-secret"
        (bundle / "run.log").write_text(f"OPENROUTER_API_KEY={fake_key}\n")
    validation = validate_bundle(bundle, expected_condition_path=CONDITION_PATH, expected_commit=COMMIT)
    assert not validation.valid
    assert any(expected in error for error in validation.errors), validation.errors
