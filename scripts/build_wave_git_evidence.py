#!/usr/bin/env python3
"""Validate and index a worker-namespaced experimental wave for Git."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


REQUIRED = ("transcript.json", "events.jsonl", "result.json", "provenance.json")
OPTIONAL = ("preliminary-status.json",)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def expected_cells(preregistration: dict) -> set[tuple[str, int, str]]:
    conditions = preregistration["conditions"].keys()
    cells = {
        (problem, seed, condition)
        for problem in preregistration["core"]["problems"]
        for seed in preregistration["core"]["seeds"]
        for condition in conditions
    }
    cells.update(
        (problem, preregistration["breadth"]["seed"], condition)
        for problem in preregistration["breadth"]["problems"]
        for condition in conditions
    )
    return cells


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--preregistration", required=True, type=Path)
    parser.add_argument("--expected-commit", required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    preregistration = json.loads(args.preregistration.read_text())
    expected = expected_cells(preregistration)

    tasks = []
    artifacts = []
    observed: set[tuple[str, int, str]] = set()
    task_ids: set[str] = set()
    counts = Counter()
    total_calls = 0
    for provenance_path in sorted(root.rglob("provenance.json")):
        provenance = json.loads(provenance_path.read_text())
        if provenance.get("git_commit") != args.expected_commit:
            raise ValueError(f"wrong commit in {provenance_path}")
        if provenance.get("experiment") != preregistration["experiment"]:
            raise ValueError(f"wrong experiment in {provenance_path}")
        task = provenance.get("task") or {}
        task_id = task.get("task_id")
        cell = (task.get("problem"), task.get("seed"), task.get("condition"))
        if not isinstance(task_id, str) or task_id in task_ids:
            raise ValueError(f"missing or duplicate task_id in {provenance_path}")
        if cell in observed:
            raise ValueError(f"duplicate cell {cell}")
        task_ids.add(task_id)
        observed.add(cell)
        task_dir = provenance_path.parent
        found = {}
        for name in REQUIRED + OPTIONAL:
            matches = list(task_dir.rglob(name))
            if name in REQUIRED and len(matches) != 1:
                raise ValueError(f"expected one {name} below {task_dir}, found {len(matches)}")
            if len(matches) > 1:
                raise ValueError(f"multiple {name} files below {task_dir}")
            if matches:
                found[name] = matches[0]
        transcript = json.loads(found["transcript.json"].read_text())
        calls = len(transcript.get("calls") or [])
        total_calls += calls
        counts[f"condition:{task['condition']}"] += 1
        counts[f"stage:{task['stage']}"] += 1
        tasks.append(
            {
                "task_id": task_id,
                "problem": task["problem"],
                "seed": task["seed"],
                "condition": task["condition"],
                "stage": task["stage"],
                "worker": provenance.get("worker"),
                "calls": calls,
                "artifact_paths": {
                    name: f"evidence/{path.relative_to(root).as_posix()}"
                    for name, path in sorted(found.items())
                },
            }
        )
        for name, path in sorted(found.items()):
            counts[f"file:{name}"] += 1
            artifacts.append(
                {
                    "git_path": f"evidence/{path.relative_to(root).as_posix()}",
                    "sha256": sha256_file(path),
                    "size_bytes": path.stat().st_size,
                }
            )

    if observed != expected:
        missing = sorted(expected - observed)
        extra = sorted(observed - expected)
        raise ValueError(f"matrix mismatch; missing={missing}, extra={extra}")
    if len(tasks) != preregistration["maximums"]["cells"]:
        raise ValueError(f"expected {preregistration['maximums']['cells']} cells, found {len(tasks)}")

    index = {
        "schema_version": 1,
        "experiment": preregistration["experiment"],
        "generating_git_commit": args.expected_commit,
        "preregistration_path": "experiments/online-development-v1/stage3-replication-v1.json",
        "matrix_validated": True,
        "cell_count": len(tasks),
        "total_calls": total_calls,
        "counts": dict(sorted(counts.items())),
        "tasks": sorted(tasks, key=lambda row: row["task_id"]),
        "artifacts": sorted(artifacts, key=lambda row: row["git_path"]),
    }
    (root / "EVIDENCE_INDEX.json").write_text(json.dumps(index, indent=2, sort_keys=True) + "\n")
    (root / "README.md").write_text(
        "# Repaired Stage 3 evidence\n\n"
        f"This branch contains all {len(tasks)} preregistered cells from "
        f"`{preregistration['experiment']}`. Its direct parent is generating code "
        f"commit `{args.expected_commit}`.\n\n"
        "Artifacts retain worker-namespaced original paths. Every cell includes "
        "`transcript.json`, `events.jsonl`, `result.json`, and `provenance.json`; "
        f"{counts['file:preliminary-status.json']} cells also include the optional "
        "`preliminary-status.json`. `EVIDENCE_INDEX.json` maps tasks to artifacts, "
        "records SHA-256 values, and confirms the preregistered matrix.\n"
    )
    print(json.dumps({"cell_count": len(tasks), "total_calls": total_calls, "counts": dict(counts)}, sort_keys=True))


if __name__ == "__main__":
    main()
