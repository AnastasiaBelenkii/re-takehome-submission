#!/usr/bin/env python3
"""Emit compact v2 matrices, paired contrasts, and morning report."""

from __future__ import annotations

import argparse
import csv
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "src"), str(ROOT)]

from collaboration_engine_v2.constants import CONDITIONS, CORE_PROBLEMS, DATASET_DEFECTS, DESIGN_ID
from re_harness.events import read_events


def result_row(task_root: Path, validation: dict[str, Any]) -> dict[str, Any]:
    provenance = json.loads((task_root / "provenance.json").read_text())
    task = provenance["task"]
    result_path = next((task_root / "outputs").rglob("result.json"))
    result = json.loads(result_path.read_text())
    events = read_events(next((task_root / "outputs").rglob("events.jsonl")))
    metadata = result.get("agent_metadata") or {}
    responses = [event for event in events if event.get("event") == "llm_response"]
    usage = [event.get("response", {}).get("usage", {}) for event in responses]
    latencies = [float(event.get("latency_ms") or 0) for event in events
                 if event.get("event") in {"llm_response", "llm_error"}]
    attempts = [attempt for track in metadata.get("tracks", {}).values()
                for attempt in track.get("attempts", [])]
    accepted = [attempt for attempt in attempts if attempt.get("accepted")]
    packet_rounds = {event["after_round"] for event in metadata.get("packet_events", [])}
    accepted_attempt = min(accepted, key=lambda item: (item["round"], item["call"])) if accepted else None
    if metadata.get("deterministic", {}).get("accepted"):
        solve_phase = "deterministic_call_zero"
    elif accepted_attempt is None:
        solve_phase = "unsolved"
    elif accepted_attempt.get("peer_packet_used"):
        solve_phase = "post_communication"
    elif any(round_number < accepted_attempt["round"] for round_number in packet_rounds):
        solve_phase = "post_communication_without_packet_use"
    else:
        solve_phase = "pre_communication"
    hashes = [attempt["candidate_sha256"] for attempt in attempts]
    signature_changes = 0
    for track in metadata.get("tracks", {}).values():
        values = [attempt["error_signature_sha256"] for attempt in track.get("attempts", [])]
        signature_changes += sum(left != right for left, right in zip(values, values[1:]))
    row = {
        **{key: task[key] for key in ("task_id", "stage", "profile", "problem", "replication", "seed", "condition")},
        "mechanical_pass": int(bool(result.get("passed"))),
        "proof_valid_recheck": int(bool(validation.get("proof_valid_recheck"))),
        "accounting_complete": int(bool(validation.get("accounting_complete"))),
        "status": result.get("status"), "calls": metadata.get("calls_dispatched", 0),
        "physical_requests": metadata.get("physical_requests", 0),
        "cost_usd": (result.get("budget") or {}).get("spent_usd", 0),
        "wall_s": result.get("wall_s", 0),
        "prompt_tokens": sum(int(item.get("prompt_tokens") or 0) for item in usage),
        "completion_tokens": sum(int(item.get("completion_tokens") or 0) for item in usage),
        "retries": metadata.get("cost_free_429_retries", 0),
        "mean_latency_ms": round(statistics.mean(latencies), 1) if latencies else 0,
        "deterministic_call_zero_solve": int(bool(metadata.get("deterministic", {}).get("accepted"))),
        "solve_phase": solve_phase, "packet_count": len(metadata.get("packet_events", [])),
        "restarts": sum(track.get("restarts", 0) for track in metadata.get("tracks", {}).values()),
        "selected_model": metadata.get("selected_model"),
        "unique_candidates": len(set(hashes)), "candidate_attempts": len(hashes),
        "error_signature_changes": signature_changes,
        "uncertain_spend_failure": int(bool(validation.get("uncertain_spend_failure"))),
        "agent_timeout": int(bool(validation.get("agent_timeout"))),
        "outer_timeout": int(bool(validation.get("outer_timeout"))),
        "comparator_timeout": int(bool(validation.get("comparator_timeout"))),
        "late_in_flight_cancellation": int(bool(validation.get("late_in_flight_cancellation"))),
    }
    return row


def score_table(rows: list[dict[str, Any]], stage: str) -> list[dict[str, Any]]:
    groups: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for row in rows:
        if row["stage"] in ({"sentinel", "core"} if stage == "core" else {stage}):
            groups[(row["problem"], row["condition"])].append(row)
    return [{"problem": problem, "condition": condition,
             "score": sum(row["mechanical_pass"] for row in values), "n": len(values),
             "proof_valid": sum(row["proof_valid_recheck"] for row in values),
             "accounting_complete_n": sum(row["accounting_complete"] for row in values)}
            for (problem, condition), values in sorted(groups.items())]


def contrasts(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    cells: dict[tuple[str, int, str, str], int] = {
        (row["problem"], row["replication"], row["profile"], row["condition"]): row["mechanical_pass"]
        for row in rows
    }
    answer = []
    for left, right in (("c1", "c0"), ("c2", "c0"), ("c2", "c1")):
        values = []
        bases = {(problem, replication, profile) for problem, replication, profile, condition in cells
                 if condition == left and (problem, replication, profile, right) in cells}
        for problem, replication, profile in sorted(bases):
            values.append(cells[(problem, replication, profile, left)] - cells[(problem, replication, profile, right)])
        answer.append({"contrast": f"{left.upper()}-{right.upper()}", "paired_n": len(values),
                       "sum_difference": sum(values),
                       "mean_difference": round(statistics.mean(values), 4) if values else None})
    return answer


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results-root", type=Path, required=True)
    args = parser.parse_args()
    reports = sorted((args.results_root / "validation").glob("*.json"),
                     key=lambda path: path.stat().st_mtime)
    latest: dict[str, dict[str, Any]] = {}
    for report_path in reports:
        for record in json.loads(report_path.read_text()).get("tasks", []):
            latest[record["task_id"]] = record
    rows = []
    for task_id, validation in latest.items():
        task_root = args.results_root / "tasks" / task_id
        if not validation.get("errors") and task_root.is_dir():
            rows.append(result_row(task_root, validation))
    rows.sort(key=lambda row: row["task_id"])
    analysis = {
        "schema_version": 1, "design_id": DESIGN_ID, "dataset_defects": list(DATASET_DEFECTS),
        "tasks": rows, "core": score_table(rows, "core"),
        "breadth": score_table(rows, "breadth"), "deep": score_table(rows, "deep"),
        "paired_contrasts": contrasts(rows),
    }
    out = args.results_root / "analysis"
    out.mkdir(parents=True, exist_ok=True)
    (out / "matrix.json").write_text(json.dumps(analysis, indent=2, sort_keys=True) + "\n")
    if rows:
        with (out / "matrix.csv").open("w", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
            writer.writeheader(); writer.writerows(rows)
    sentinel = [row for row in rows if row["stage"] == "sentinel"]
    sentinel_lines = ["# Sentinel status", "", "| Condition | Pass | Recheck | Status | Calls | Cost |",
                      "|---|---:|---:|---|---:|---:|"]
    sentinel_lines += [f"| {row['condition'].upper()} | {row['mechanical_pass']} | {row['proof_valid_recheck']} | {row['status']} | {row['calls']} | ${row['cost_usd']:.6f} |"
                       for row in sentinel]
    (out / "SENTINEL.md").write_text("\n".join(sentinel_lines) + "\n")
    lines = ["# Collaboration engine v2 morning report", "",
             f"Validated cells: {len(rows)}/87. Dataset defect excluded: `{DATASET_DEFECTS[0]}`.", "",
             "## Paired intention-to-treat contrasts", "",
             "| Contrast | Paired n | Sum difference | Mean difference |", "|---|---:|---:|---:|"]
    for item in analysis["paired_contrasts"]:
        mean = "n/a" if item["mean_difference"] is None else f'{item["mean_difference"]:.4f}'
        lines.append(f"| {item['contrast']} | {item['paired_n']} | {item['sum_difference']} | {mean} |")
    for label in ("core", "breadth", "deep"):
        lines += ["", f"## {label.title()} scores", "", "| Problem | Condition | ITT score | Proof-valid | Accounting complete |",
                  "|---|---|---:|---:|---:|"]
        for item in analysis[label]:
            lines.append(f"| {item['problem']} | {item['condition'].upper()} | {item['score']}/{item['n']} | {item['proof_valid']}/{item['n']} | {item['accounting_complete_n']}/{item['n']} |")
    lines += ["", "Primary scores are intention-to-treat; proof-valid and accounting-complete counts are separate sensitivity views."]
    (out / "MORNING.md").write_text("\n".join(lines) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
