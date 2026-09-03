#!/usr/bin/env python3
"""Validate raw v2 tasks and independently recheck proofs with Comparator."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import uuid
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "src"), str(ROOT)]

from collaboration_engine_v2.constants import DESIGN_ID
from collaboration_engine_v2.experiment import LEAN_IMAGE
from re_harness.events import read_events
from re_harness.lean import compare_solution, numeric_answers_are_literals
from re_harness.manifest import ProblemSpec


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def one_file(root: Path, name: str) -> Path:
    matches = list(root.rglob(name))
    if len(matches) != 1:
        raise ValueError(f"expected one {name}, found {len(matches)}")
    return matches[0]


def terminal_by_call(events: list[dict[str, Any]]) -> tuple[int, int, int]:
    requests = [event for event in events if event.get("event") == "llm_request"]
    terminal = [event for event in events if event.get("event") in {"llm_response", "llm_error"}]
    request_ids = {event.get("call_id") for event in requests}
    terminal_ids = {event.get("call_id") for event in terminal}
    return len(requests), len(terminal), len(request_ids - terminal_ids)


def eligible_rounds(metadata: dict[str, Any]) -> list[int]:
    by_round: dict[int, list[dict[str, Any]]] = {}
    for track in metadata.get("tracks", {}).values():
        for attempt in track.get("attempts", []):
            by_round.setdefault(int(attempt["round"]), []).append(attempt)
    return sorted(round_number for round_number, attempts in by_round.items()
                  if len(attempts) == 2 and not any(item.get("accepted") for item in attempts))


def validate_task(task_root: Path, secret: str) -> dict[str, Any]:
    errors: list[str] = []
    provenance_path = task_root / "provenance.json"
    if not provenance_path.is_file():
        raise ValueError("missing provenance.json")
    provenance = json.loads(provenance_path.read_text())
    result_path, events_path, solution_path = (one_file(task_root / "outputs", name)
                                               for name in ("result.json", "events.jsonl", "solution.lean"))
    result = json.loads(result_path.read_text())
    events = read_events(events_path)
    metadata = result.get("agent_metadata") or {}
    task = provenance.get("task") or {}
    if provenance.get("design_id") != DESIGN_ID or metadata.get("design_id") != DESIGN_ID:
        errors.append("design identity mismatch")
    if result.get("problem_id") != task.get("problem"):
        errors.append("problem identity mismatch")
    if not isinstance(result.get("status"), str):
        errors.append("missing status")
    physical, terminals, unmatched = terminal_by_call(events)
    semantic = metadata.get("calls_dispatched")
    retries = metadata.get("cost_free_429_retries", 0)
    if physical != metadata.get("physical_requests") or physical != semantic + retries:
        errors.append("semantic/physical call reconciliation failed")
    retry_errors = [event for event in events if event.get("event") == "llm_error"
                    and event.get("status_code") == 429 and event.get("cost_status") == "none"]
    if len(retry_errors) < retries:
        errors.append("retry count lacks typed cost-free 429 events")
    packets = metadata.get("packet_events", [])
    condition = task.get("condition")
    eligible = eligible_rounds(metadata)
    pair_rounds: dict[int, int] = {}
    for packet in packets:
        pair_rounds[packet["after_round"]] = pair_rounds.get(packet["after_round"], 0) + 1
    if condition == "c0" and packets:
        errors.append("C0 emitted packets")
    if condition == "c1":
        expected = {eligible[0]: 2} if eligible else {}
        if pair_rounds != expected:
            errors.append("C1 cadence mismatch")
    if condition == "c2" and pair_rounds != {round_number: 2 for round_number in eligible}:
        errors.append("C2 cadence mismatch")
    text_paths = [path for path in task_root.rglob("*") if path.is_file()
                  and path.name != "run.pid" and path.stat().st_size <= 5_000_000]
    for path in text_paths:
        text = path.read_text(encoding="utf-8", errors="ignore")
        if "OPENROUTER_API_KEY" in text or (secret and secret in text):
            errors.append(f"secret material in {path.relative_to(task_root)}")
            break

    manifest = json.loads((task_root / "problem-set/manifest.json").read_text())
    spec_raw = manifest["problems"][0]
    challenge = (task_root / "problem-set" / task["problem"] / "challenge.lean").read_text()
    solution = solution_path.read_text()
    spec = ProblemSpec(
        id=spec_raw["id"], theorem_names=tuple(spec_raw.get("theorem_names", [])),
        definition_names=tuple(spec_raw.get("definition_names", [])),
        numeric_answer_names=tuple(spec_raw.get("numeric_answer_names", [])),
        metadata=spec_raw.get("metadata", {}),
    )
    verdict = compare_solution(image=LEAN_IMAGE, session_id=uuid.uuid4().hex,
                               challenge=challenge, solution=solution, spec=spec, timeout_s=180)
    answer_ok, _answer_errors = numeric_answers_are_literals(solution, spec.numeric_answer_names)
    proof_valid = bool(verdict.passed and answer_ok)
    uncertain = any(event.get("event") == "llm_error" and event.get("cost_status") == "unknown"
                    for event in events)
    comparator = result.get("comparator") or {}
    agent_error = result.get("agent_error") or {}
    outer_timeout = result.get("status") == "timed_out" and agent_error.get("type") == "timed_out"
    record = {
        "task_id": task.get("task_id"), "stage": task.get("stage"),
        "problem": task.get("problem"), "replication": task.get("replication"),
        "condition": condition, "seed": task.get("seed"),
        "mechanical_pass": bool(result.get("passed")),
        "proof_valid_recheck": proof_valid,
        "proof_recheck_timed_out": bool(verdict.timed_out),
        "accounting_complete": bool((result.get("budget") or {}).get("accounting_complete")),
        "cost_free_429_retries": retries, "uncertain_spend_failure": uncertain,
        "agent_timeout": result.get("status") == "agent_timeout" or agent_error.get("type") == "TimeoutError",
        "outer_timeout": outer_timeout, "comparator_timeout": bool(comparator.get("timed_out")),
        "late_in_flight_cancellation": bool(unmatched and result.get("status") in {"timed_out", "agent_timeout"}),
        "semantic_calls": semantic, "physical_requests": physical,
        "terminal_request_events": terminals, "unmatched_requests": unmatched,
        "packet_count": len(packets), "eligible_packet_rounds": eligible,
        "status": result.get("status"), "errors": errors,
    }
    checksums = {str(path.relative_to(task_root)): sha256(path) for path in sorted(task_root.rglob("*"))
                 if path.is_file() and path.name not in {"checksums.json"}}
    (task_root / "checksums.json").write_text(json.dumps(checksums, indent=2, sort_keys=True) + "\n")
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results-root", type=Path, required=True)
    parser.add_argument("--task", action="append", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    secret = ""
    env_path = ROOT / ".env"
    if env_path.is_file():
        for line in env_path.read_text().splitlines():
            if line.startswith("OPENROUTER_API_KEY="):
                secret = line.partition("=")[2].strip().strip('"\'')
    records = []
    for task_id in args.task:
        try:
            records.append(validate_task(args.results_root / "tasks" / task_id, secret))
        except Exception as exc:
            records.append({"task_id": task_id, "errors": [f"{type(exc).__name__}: {exc}"],
                            "mechanical_pass": False, "proof_valid_recheck": False})
    report = {"schema_version": 1, "design_id": DESIGN_ID, "validated_at": __import__("datetime").datetime.now(__import__("datetime").timezone.utc).isoformat(),
              "valid": all(not record["errors"] for record in records), "tasks": records}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    return 0 if report["valid"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
