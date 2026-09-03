#!/usr/bin/env python3
"""Run a frozen sequence of microcell descriptors on one remote worker.

This controller is deliberately worker-local: once launched, loss of the
dispatching host cannot prevent later cells in the queue from starting.
It never retries an ambiguous launch and never overwrites a task directory.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def atomic(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worktree", type=Path, required=True)
    parser.add_argument("--queue", type=Path, required=True)
    parser.add_argument("--run-root", type=Path, required=True)
    parser.add_argument("--poll-seconds", type=float, default=2)
    parser.add_argument(
        "--launch-deadline", type=str,
        help="absolute ISO-8601 time after which pending cells are recorded as skipped",
    )
    args = parser.parse_args()

    worktree = args.worktree.resolve()
    queue_path = args.queue.resolve()
    run_root = args.run_root.resolve()
    launch_deadline = datetime.fromisoformat(args.launch_deadline) if args.launch_deadline else None
    queue = json.loads(queue_path.read_text())
    if queue.get("schema_version") != 1 or not queue.get("descriptors"):
        raise ValueError("invalid or empty frozen queue")
    descriptors = [Path(item).resolve() for item in queue["descriptors"]]
    task_ids = [json.loads(path.read_text())["task"]["task_id"] for path in descriptors]
    if len(task_ids) != len(set(task_ids)):
        raise ValueError("queue contains duplicate task IDs")

    state_path = run_root / "queue-state.json"
    if state_path.exists():
        state = json.loads(state_path.read_text())
        if state.get("task_ids") != task_ids:
            raise ValueError("existing state differs from frozen queue")
        if any(item["status"] == "dispatching" for item in state["tasks"].values()):
            raise RuntimeError("ambiguous prior dispatch; manual reconciliation required")
    else:
        state = {
            "schema_version": 1,
            "experiment": queue["experiment"],
            "worker": queue["worker"],
            "created_at": now(),
            "updated_at": now(),
            "phase": "running",
            "task_ids": task_ids,
            "tasks": {task_id: {"status": "pending"} for task_id in task_ids},
        }
        atomic(state_path, state)

    launcher = worktree / "scripts" / "launch_online_microcell.py"
    python = worktree / ".venv" / "bin" / "python"
    for descriptor_path, task_id in zip(descriptors, task_ids, strict=True):
        cell = state["tasks"][task_id]
        task_root = run_root / "tasks" / task_id
        if cell["status"] in {"complete", "exited_incomplete"}:
            continue
        if cell["status"] == "running":
            # A restarted controller may only adopt a launch with a terminal
            # marker. A live or vanished ambiguous process requires a human.
            status_path = task_root / "microcell-status.json"
            if not status_path.exists():
                raise RuntimeError(f"ambiguous running cell: {task_id}")
        else:
            if launch_deadline is not None and datetime.now(timezone.utc) >= launch_deadline:
                cell.update({"status": "skipped_deadline", "at": now()})
                for remaining_id in task_ids[task_ids.index(task_id) + 1:]:
                    if state["tasks"][remaining_id]["status"] == "pending":
                        state["tasks"][remaining_id] = {
                            "status": "skipped_deadline", "at": now()
                        }
                state["phase"] = "deadline"
                state["updated_at"] = now()
                atomic(state_path, state)
                return 0
            if task_root.exists():
                raise RuntimeError(f"refusing existing task directory: {task_root}")
            descriptor = json.loads(descriptor_path.read_text())
            not_before = datetime.fromisoformat(descriptor["not_before"])
            while datetime.now(timezone.utc) < not_before:
                time.sleep(min(10, max(1, (not_before - datetime.now(timezone.utc)).total_seconds())))
            cell.update({"status": "dispatching", "at": now()})
            state["updated_at"] = now()
            atomic(state_path, state)
            runtime_descriptor = run_root / "runtime-dispatch" / descriptor_path.name
            descriptor["dispatched_at"] = now()
            atomic(runtime_descriptor, descriptor)
            output = subprocess.run(
                [str(python), str(launcher), "--worktree", str(worktree),
                 "--descriptor", str(runtime_descriptor), "--task-root", str(task_root)],
                cwd=worktree, check=True, text=True, stdout=subprocess.PIPE,
            ).stdout
            launch = json.loads(output.strip().splitlines()[-1])
            cell.update({"status": "running", "pid": launch["pid"], "launched_at": now()})
            state["updated_at"] = now()
            atomic(state_path, state)

        status_path = task_root / "microcell-status.json"
        while not status_path.exists():
            time.sleep(max(1, args.poll_seconds))
        terminal = json.loads(status_path.read_text())
        cell.update({
            "status": "complete" if terminal.get("result_artifact_count") == 1 else "exited_incomplete",
            "finished_at": now(),
            "terminal": terminal,
        })
        state["updated_at"] = now()
        atomic(state_path, state)

    state["phase"] = (
        "collected_remote"
        if all(item["status"] == "complete" for item in state["tasks"].values())
        else "incomplete"
    )
    state["updated_at"] = now()
    atomic(state_path, state)
    return 0 if state["phase"] == "collected_remote" else 4


if __name__ == "__main__":
    raise SystemExit(main())
