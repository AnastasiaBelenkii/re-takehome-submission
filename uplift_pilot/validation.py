"""Validation for self-contained uplift pilot run bundles."""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from uplift_pilot.constants import DESIGN_ID
from uplift_pilot.experiment import (
    EXPECTED_CONDITIONS,
    EXPECTED_PROBLEMS,
    Condition,
    load_condition,
    sha256_file,
)


SECRET_PATTERNS = (
    re.compile(rb"sk-or-v1-[A-Za-z0-9_-]{12,}"),
    re.compile(rb"(?i)authorization\s*[:=]\s*bearer\s+(?!\[REDACTED\])[A-Za-z0-9._-]{12,}"),
    re.compile(rb"(?i)OPENROUTER_API_KEY\s*=\s*(?!\[REDACTED\]|['\"]?\s*$)[^\s'\"]{12,}"),
)


@dataclass(frozen=True)
class ValidationResult:
    valid: bool
    errors: tuple[str, ...]
    report: dict[str, Any]
    table: str
    checksums: dict[str, str]


def _read_json(path: Path, errors: list[str], label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        errors.append(f"{label}: unreadable JSON: {exc}")
        return {}
    if not isinstance(value, dict):
        errors.append(f"{label}: expected a JSON object")
        return {}
    return value


def _read_events(path: Path, errors: list[str], problem_id: str) -> list[dict[str, Any]]:
    if not path.is_file():
        errors.append(f"{problem_id}: missing events.jsonl")
        return []
    events = []
    for index, line in enumerate(path.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        if not line.strip():
            continue
        try:
            event = json.loads(line)
        except json.JSONDecodeError as exc:
            errors.append(f"{problem_id}: events.jsonl line {index} is invalid: {exc}")
            continue
        if isinstance(event, dict):
            events.append(event)
        else:
            errors.append(f"{problem_id}: events.jsonl line {index} is not an object")
    return events


def _checksums(bundle: Path) -> dict[str, str]:
    excluded = {"checksums.sha256", "validation.json", "validation.txt"}
    values = {}
    for path in sorted(item for item in bundle.rglob("*") if item.is_file() and item.name not in excluded):
        values[str(path.relative_to(bundle))] = sha256_file(path)
    return values


def _scan_secrets(bundle: Path, errors: list[str]) -> None:
    for path in sorted(item for item in bundle.rglob("*") if item.is_file()):
        if path.name == "checksums.sha256":
            continue
        try:
            data = path.read_bytes()
        except OSError as exc:
            errors.append(f"cannot secret-scan {path.relative_to(bundle)}: {exc}")
            continue
        if any(pattern.search(data) for pattern in SECRET_PATTERNS):
            errors.append(f"apparent API key or authorization secret in {path.relative_to(bundle)}")


def _close_enough(left: Any, right: Any) -> bool:
    try:
        return abs(float(left) - float(right)) < 1e-7
    except (TypeError, ValueError):
        return False


def validate_bundle(
    bundle: Path,
    *,
    expected_condition_path: Path,
    expected_commit: str,
) -> ValidationResult:
    bundle = bundle.resolve()
    errors: list[str] = []
    if not re.fullmatch(r"[0-9a-f]{40}", expected_commit):
        errors.append("expected commit must be a full 40-character lowercase Git SHA")
    try:
        condition: Condition = load_condition(expected_condition_path)
        for condition_id in EXPECTED_CONDITIONS:
            load_condition(condition.path.parent / f"{condition_id}.json")
    except ValueError as exc:
        condition = None  # type: ignore[assignment]
        errors.append(f"expected condition invalid: {exc}")

    provenance = _read_json(bundle / "provenance.json", errors, "provenance.json")
    bundled_condition_path = bundle / "condition.json"
    if not bundled_condition_path.is_file():
        errors.append("missing condition.json")
    run_log = bundle / "run.log"
    pid_path = bundle / "run.pid"
    if not run_log.is_file():
        errors.append("missing run.log")
    if not pid_path.is_file():
        errors.append("missing run.pid")
    if not (bundle / "outputs").is_dir():
        errors.append("missing outputs directory")

    if condition is not None:
        expected_manifest_hash = condition.manifest_sha256
        expected_problem_path = condition.path.parent.parent / "problems.txt"
        expected_launcher_path = condition.path.parents[3] / "scripts" / "launch_uplift_pilot.py"
        if bundled_condition_path.is_file() and sha256_file(bundled_condition_path) != expected_manifest_hash:
            errors.append("condition.json does not exactly match the expected static manifest")
        expectations = {
            "experiment": "uplift-pilot-v1",
            "design_id": DESIGN_ID,
            "condition": condition.condition,
            "model": condition.model,
            "policy": condition.policy,
            "git_commit": expected_commit,
            "manifest_sha256": expected_manifest_hash,
            "problem_list_sha256": sha256_file(expected_problem_path),
            "lean_image": condition.resources["lean_image"],
        }
        if expected_launcher_path.is_file():
            expectations["launcher_sha256"] = sha256_file(expected_launcher_path)
        for key, expected in expectations.items():
            if provenance.get(key) != expected:
                errors.append(f"provenance {key} mismatch: expected {expected!r}, found {provenance.get(key)!r}")
        effective = provenance.get("effective_configuration")
        if not isinstance(effective, dict):
            errors.append("provenance effective_configuration is missing or invalid")
        else:
            expected_effective = condition.effective_configuration(
                problems_path=Path(str(effective.get("problems", ""))),
                output_root=Path(str(effective.get("output_root", ""))),
            )
            if effective != expected_effective:
                errors.append("effective configuration does not match the condition manifest")
            command = provenance.get("command")
            if not isinstance(command, list) or "--agent" not in command or condition.condition not in effective["environment"].get("UPLIFT_CONDITION", ""):
                errors.append("recorded command/effective environment is incomplete")

    run_paths = sorted((bundle / "outputs").rglob("run.json")) if (bundle / "outputs").is_dir() else []
    if len(run_paths) != 1:
        errors.append(f"expected exactly one run.json under outputs, found {len(run_paths)}")
        run_dir = bundle / "outputs"
        run_json: dict[str, Any] = {}
    else:
        run_dir = run_paths[0].parent
        run_json = _read_json(run_paths[0], errors, "run.json")
    summary = _read_json(run_dir / "summary.json", errors, "summary.json")
    if not run_json.get("finished_at"):
        errors.append("run.json finished_at is null or absent")
    if not summary.get("finished_at"):
        errors.append("summary.json finished_at is null or absent")
    if run_json.get("finished_at") and summary.get("finished_at") and run_json["finished_at"] != summary["finished_at"]:
        errors.append("run.json and summary.json finished_at disagree")
    summary_rows = summary.get("problems", [])
    summary_by_id = {
        row.get("problem_id"): row for row in summary_rows if isinstance(row, dict) and isinstance(row.get("problem_id"), str)
    } if isinstance(summary_rows, list) else {}
    if set(summary_by_id) != set(EXPECTED_PROBLEMS) or len(summary_by_id) != 6:
        errors.append("summary must contain all and only the six declared problems")

    rows: list[dict[str, Any]] = []
    score = 0
    total_cost = 0.0
    status_counts: dict[str, int] = {}
    for problem_id in EXPECTED_PROBLEMS:
        problem_dir = run_dir / problem_id
        result = _read_json(problem_dir / "result.json", errors, f"{problem_id}/result.json")
        transcript = _read_json(problem_dir / "transcript.json", errors, f"{problem_id}/transcript.json")
        if not (problem_dir / "solution.lean").is_file():
            errors.append(f"{problem_id}: missing solution.lean")
        events = _read_events(problem_dir / "events.jsonl", errors, problem_id)
        if result.get("problem_id") != problem_id:
            errors.append(f"{problem_id}: result problem_id mismatch")
        status = str(result.get("status", "missing"))
        if status == "missing":
            errors.append(f"{problem_id}: status is missing")
        status_counts[status] = status_counts.get(status, 0) + 1
        request_events = [event for event in events if event.get("event") == "llm_request"]
        transcript_calls = transcript.get("calls", [])
        if not isinstance(transcript_calls, list):
            transcript_calls = []
            errors.append(f"{problem_id}: transcript calls must be a list")
        if len(request_events) != len(transcript_calls):
            errors.append(f"{problem_id}: events/transcript call counts disagree")
        event_call_ids = [str(event.get("call_id", "")) for event in request_events]
        transcript_call_ids = [str(call.get("call_id", "")) for call in transcript_calls if isinstance(call, dict)]
        if event_call_ids != transcript_call_ids:
            errors.append(f"{problem_id}: events/transcript call identities or order disagree")
        max_calls = condition.resources["max_calls"] if condition is not None else 25
        if len(request_events) > max_calls:
            errors.append(f"{problem_id}: {len(request_events)} calls exceed ceiling {max_calls}")
        event_models = {
            event.get("request", {}).get("model")
            for event in request_events
            if isinstance(event.get("request"), dict)
        }
        result_models = set(result.get("models_used", [])) if isinstance(result.get("models_used"), list) else set()
        if event_models != result_models:
            errors.append(f"{problem_id}: result models_used disagrees with events")
        if condition is not None and any(model != condition.model for model in event_models):
            errors.append(f"{problem_id}: model does not match condition {condition.model}")
        metadata = result.get("agent_metadata", {})
        if isinstance(metadata, dict) and metadata:
            for key, expected in (("design_id", DESIGN_ID), ("condition", condition.condition if condition else None), ("model", condition.model if condition else None)):
                if expected is not None and metadata.get(key) != expected:
                    errors.append(f"{problem_id}: agent_metadata {key} mismatch")
            if int(metadata.get("calls_dispatched", len(request_events))) != len(request_events):
                errors.append(f"{problem_id}: agent call count disagrees with events")
        row = summary_by_id.get(problem_id, {})
        passed = bool(result.get("passed"))
        cost = float(result.get("budget", {}).get("spent_usd", 0.0)) if isinstance(result.get("budget"), dict) else 0.0
        event_cost = sum(
            float(event.get("actual_cost_usd") or 0.0)
            for event in events
            if event.get("event") == "llm_response"
        )
        if not _close_enough(transcript.get("actual_cost_usd"), event_cost):
            errors.append(f"{problem_id}: events and transcript cost disagree")
        if not _close_enough(cost, event_cost):
            errors.append(f"{problem_id}: result budget and recorded response cost disagree")
        if row:
            if row.get("status") != status or bool(row.get("passed")) != passed:
                errors.append(f"{problem_id}: result and summary status/pass disagree")
            if not _close_enough(row.get("actual_cost_usd"), cost):
                errors.append(f"{problem_id}: result and summary cost disagree")
        score += int(passed)
        total_cost += cost
        rows.append({"problem": problem_id, "status": status, "score": int(passed), "calls": len(request_events), "cost_usd": round(cost, 10)})

    if summary and int(summary.get("total_points", -1)) != score:
        errors.append("summary total_points disagrees with results")
    if summary and not _close_enough(summary.get("actual_cost_usd"), total_cost):
        errors.append("summary actual_cost_usd disagrees with results")
    _scan_secrets(bundle, errors)
    checksums = _checksums(bundle)
    table_lines = ["problem                 status          score calls cost_usd", "----------------------- --------------- ----- ----- --------"]
    for row in rows:
        table_lines.append(
            f"{row['problem']:<23} {row['status']:<15} {row['score']:>5} {row['calls']:>5} {row['cost_usd']:>8.4f}"
        )
    table_lines.append(f"TOTAL{'':<42} {score:>5} {'':>5} {total_cost:>8.4f}")
    report = {
        "schema_version": 1,
        "bundle": str(bundle),
        "condition": condition.condition if condition else None,
        "commit": expected_commit,
        "valid": not errors,
        "errors": errors,
        "score": score,
        "max_score": 6,
        "cost_usd": round(total_cost, 10),
        "status_counts": status_counts,
        "problems": rows,
        "checksum_count": len(checksums),
    }
    return ValidationResult(not errors, tuple(errors), report, "\n".join(table_lines) + "\n", checksums)


def write_validation_artifacts(bundle: Path, validation: ValidationResult) -> None:
    bundle = bundle.resolve()
    (bundle / "validation.json").write_text(
        json.dumps(validation.report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    text = ("VALID\n" if validation.valid else "INVALID\n") + validation.table
    if validation.errors:
        text += "\nReasons:\n" + "".join(f"- {error}\n" for error in validation.errors)
    (bundle / "validation.txt").write_text(text, encoding="utf-8")
    (bundle / "checksums.sha256").write_text(
        "".join(f"{digest}  {relative}\n" for relative, digest in sorted(validation.checksums.items())),
        encoding="utf-8",
    )


def append_ledger(ledger: Path, validation: ValidationResult, provenance: dict[str, Any]) -> None:
    ledger.parent.mkdir(parents=True, exist_ok=True)
    existing = ledger.read_text(encoding="utf-8").splitlines() if ledger.exists() else []
    run_id = None
    bundle = Path(validation.report["bundle"])
    run_paths = list((bundle / "outputs").rglob("run.json"))
    if len(run_paths) == 1:
        try:
            run_id = json.loads(run_paths[0].read_text(encoding="utf-8")).get("run_id")
        except (OSError, json.JSONDecodeError):
            pass
    for line in existing:
        try:
            entry = json.loads(line)
        except json.JSONDecodeError:
            raise ValueError("ledger contains invalid JSON and must not be rewritten")
        if entry.get("artifact_path") == str(bundle) or (run_id and entry.get("run_id") == run_id):
            raise ValueError("ledger already contains this run; refusing duplicate append")
    payload = {
        "schema_version": 1,
        "run_id": run_id,
        "condition": validation.report["condition"],
        "commit": validation.report["commit"],
        "host": provenance.get("host", {}).get("hostname"),
        "launched_at": provenance.get("launched_at"),
        "finished_at": None,
        "status": "validated" if validation.valid else "invalid",
        "validation_passed": validation.valid,
        "validation_errors": list(validation.errors),
        "score": validation.report["score"],
        "cost_usd": validation.report["cost_usd"],
        "artifact_path": str(bundle),
    }
    if len(run_paths) == 1:
        try:
            payload["finished_at"] = json.loads(run_paths[0].read_text(encoding="utf-8")).get("finished_at")
        except (OSError, json.JSONDecodeError):
            pass
    with ledger.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, sort_keys=True) + "\n")
