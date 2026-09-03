#!/usr/bin/env python3
"""Persistently drain the 27-cell corrected v2 addendum through one remote slot."""

from __future__ import annotations

import argparse
import json
import os
import shlex
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

CONFIRMATION = "I_UNDERSTAND_THIS_LAUNCHES_PAID_CORRECTED_V2_CELLS"
CONDITIONS = ("c0", "c1", "c2")
PROBLEMS = ("rmo_2000_6", "putnam_2020_a2", "putnam_2018_a1")
SEEDS = (1729, 2718, 3141)
STRATEGIES = {
    "c0": "none",
    "c1": "reciprocal-once-v1",
    "c2": "reciprocal-every-eligible-v1",
}


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def atomic(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def ssh(worker: str, command: str) -> str:
    result = subprocess.run(
        ["ssh", "-o", "BatchMode=yes", worker, "bash", "-lc", shlex.quote(command)],
        check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    return result.stdout


def queue() -> list[dict[str, Any]]:
    tasks = []
    for replication, seed in enumerate(SEEDS, 1):
        for problem_index, problem in enumerate(PROBLEMS):
            for offset in range(3):
                condition = CONDITIONS[(problem_index + replication - 1 + offset) % 3]
                tasks.append({
                    "task_id": f"corrected-{problem}-r{replication}-{condition}",
                    "stage": "corrected", "profile": "shallow", "problem": problem,
                    "replication": replication, "seed": seed, "condition": condition,
                    "strategy": STRATEGIES[condition],
                })
    assert len(tasks) == 27
    return tasks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--results-root", type=Path, required=True)
    parser.add_argument("--worker", required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--worktree", required=True)
    parser.add_argument("--helper", required=True)
    parser.add_argument("--validation-python", required=True)
    parser.add_argument("--validation-script", required=True)
    parser.add_argument("--confirm-paid-launch")
    parser.add_argument("--poll-seconds", type=float, default=5)
    args = parser.parse_args()
    if args.confirm_paid_launch != CONFIRMATION:
        raise SystemExit(f"confirmation required: {CONFIRMATION}")
    tasks = queue()
    if args.state.exists():
        state = json.loads(args.state.read_text())
        if state.get("queue") != tasks or state.get("commit") != args.commit:
            raise SystemExit("resume state differs from the frozen addendum")
    else:
        state = {
            "schema_version": 1, "created_at": now(), "updated_at": now(),
            "commit": args.commit, "worker": args.worker, "queue": tasks,
            "tasks": {task["task_id"]: {"status": "pending"} for task in tasks},
            "phase": "running",
        }
        atomic(args.state, state)

    while True:
        running = next((task for task in tasks
                        if state["tasks"][task["task_id"]]["status"] == "running"), None)
        if running is not None:
            cell = state["tasks"][running["task_id"]]
            remote_root = cell["remote_root"]
            output = ssh(args.worker,
                         f"test -f {shlex.quote(remote_root + '/remote-task-status.json')} "
                         f"&& cat {shlex.quote(remote_root + '/remote-task-status.json')} || true")
            if output.strip():
                terminal = json.loads(output)
                local_root = args.results_root / "tasks" / running["task_id"]
                local_root.parent.mkdir(parents=True, exist_ok=True)
                subprocess.run([
                    "rsync", "-a", "--partial", "-e", "ssh -o BatchMode=yes",
                    f"{args.worker}:{remote_root}/", f"{local_root}/",
                ], check=True)
                cell.update({
                    "status": "complete" if terminal["exit_code"] == 0 else "exited_incomplete",
                    "exit_code": terminal["exit_code"], "finished_at": terminal["finished_at"],
                    "local_root": str(local_root),
                })
                state["updated_at"] = now()
                atomic(args.state, state)
            else:
                time.sleep(max(1, args.poll_seconds))
                continue

        incomplete = [task for task in tasks
                      if state["tasks"][task["task_id"]]["status"] == "exited_incomplete"]
        if incomplete:
            state["phase"] = "incomplete"
            state["updated_at"] = now()
            atomic(args.state, state)
            return 4
        pending = next((task for task in tasks
                        if state["tasks"][task["task_id"]]["status"] == "pending"), None)
        if pending is None:
            report = args.results_root / "validation.json"
            command = [args.validation_python, args.validation_script,
                       "--results-root", str(args.results_root), "--output", str(report)]
            for task in tasks:
                command.extend(["--task", task["task_id"]])
            validation = subprocess.run(command)
            state["validation"] = {
                "exit_code": validation.returncode, "report": str(report),
                "finished_at": now(),
            }
            state["phase"] = "complete" if validation.returncode == 0 else "integrity_failed"
            state["updated_at"] = now()
            atomic(args.state, state)
            return 0 if validation.returncode == 0 else 5

        task_id = pending["task_id"]
        descriptor_dir = args.results_root / "dispatch"
        descriptor = descriptor_dir / f"{task_id}.json"
        atomic(descriptor, {
            "task": pending, "git_commit": args.commit, "dispatched_at": now(),
            "worker": args.worker, "recovery": False, "corrected_addendum": True,
            "upstream_fixes": ["6a33f70", "7b245af"],
        })
        remote_descriptor = f"{args.results_root}/remote-dispatch/{task_id}.json"
        remote_root = f"{args.results_root}/remote-tasks/{task_id}"
        state["tasks"][task_id] = {
            "status": "dispatching", "worker": args.worker,
            "remote_root": remote_root, "at": now(),
        }
        state["updated_at"] = now()
        atomic(args.state, state)
        ssh(args.worker, f"mkdir -p {shlex.quote(str(args.results_root) + '/remote-dispatch')}")
        subprocess.run(["scp", "-q", "-o", "BatchMode=yes", str(descriptor),
                        f"{args.worker}:{remote_descriptor}"], check=True)
        output = ssh(
            args.worker,
            f"{shlex.quote(args.worktree + '/.venv/bin/python')} {shlex.quote(args.helper)} "
            f"--worktree {shlex.quote(args.worktree)} --descriptor {shlex.quote(remote_descriptor)} "
            f"--task-root {shlex.quote(remote_root)}",
        )
        launch = json.loads(output.strip().splitlines()[-1])
        state["tasks"][task_id].update({"status": "running", "pid": launch["pid"]})
        state["updated_at"] = now()
        atomic(args.state, state)
        time.sleep(max(1, args.poll_seconds))


if __name__ == "__main__":
    raise SystemExit(main())
