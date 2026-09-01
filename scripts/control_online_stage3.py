#!/usr/bin/env python3
"""Resumably dispatch the matched 84-cell Stage 3 matrix to three worker trios."""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import subprocess
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


CONFIRMATION = "I_UNDERSTAND_THIS_LAUNCHES_PAID_STAGE3_CELLS"


@dataclass(frozen=True)
class Task:
    task_id: str
    block_id: str
    group: int
    stage: str
    profile: str
    problem: str
    replication: int
    seed: int
    condition: str
    strategy: str
    worker: str


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def atomic(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def run(argv: list[str], *, capture: bool = False) -> str:
    result = subprocess.run(
        argv,
        check=True,
        text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
    )
    return result.stdout if capture else ""


def ssh(worker: str, command: str) -> str:
    return run(
        ["ssh", "-o", "BatchMode=yes", worker, "bash", "-lc", shlex.quote(command)],
        capture=True,
    )


def build_tasks(plan: dict[str, Any]) -> list[Task]:
    conditions = plan["conditions"]
    groups = plan["worker_groups"]
    blocks: list[tuple[str, int, str, int]] = []
    for replication, seed in enumerate(plan["core"]["seeds"], 1):
        blocks.extend(("core", replication, problem, seed) for problem in plan["core"]["problems"])
    blocks.extend(
        ("breadth", 1, problem, plan["breadth"]["seed"])
        for problem in plan["breadth"]["problems"]
    )
    tasks: list[Task] = []
    names = tuple(conditions)
    for block_index, (stage, replication, problem, seed) in enumerate(blocks):
        group = block_index % len(groups)
        group_sequence = block_index // len(groups)
        block_id = f"{stage}-{problem}-r{replication}"
        for offset, condition in enumerate(names):
            worker = groups[group][(offset + group_sequence) % len(groups[group])]
            tasks.append(Task(
                task_id=f"stage3v1-{block_id}-{condition}",
                block_id=block_id,
                group=group,
                stage=stage,
                profile="shallow",
                problem=problem,
                replication=replication,
                seed=seed,
                condition=condition,
                strategy=conditions[condition],
                worker=worker,
            ))
    return tasks


def validate_plan(plan: dict[str, Any], tasks: list[Task], commit: str) -> None:
    if plan.get("schema_version") != 1:
        raise ValueError("unsupported plan schema")
    if len(tasks) != 84 or len({task.task_id for task in tasks}) != 84:
        raise ValueError("Stage 3 plan must contain exactly 84 unique cells")
    workers = {task.worker for task in tasks}
    if workers != {f"takehome-worker-{index}" for index in range(1, 10)}:
        raise ValueError("Stage 3 must use workers 1-9 exactly")
    if any(task.worker == "takehome-worker-10" for task in tasks):
        raise ValueError("worker 10 is prohibited")
    for block_id in {task.block_id for task in tasks}:
        block = [task for task in tasks if task.block_id == block_id]
        if len(block) != 3 or {task.condition for task in block} != {"c0", "c1", "c2"}:
            raise ValueError(f"unmatched block: {block_id}")
    manifest = json.loads(Path("sample-problems/manifest.json").read_text())
    declared = set(plan["core"]["problems"]) | set(plan["breadth"]["problems"])
    available = {item["id"] for item in manifest["problems"]}
    if declared != available or len(declared) != 16:
        raise ValueError("plan does not partition the current 16-problem manifest")
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("commit must be a full SHA")
    head = run(["git", "rev-parse", "HEAD"], capture=True).strip()
    if head != commit:
        raise ValueError("commit is not the checked-out source")
    if run(["git", "status", "--porcelain", "--untracked-files=all"], capture=True).strip():
        raise ValueError("source tree must be clean")


def remote_status(task: Task, remote_root: str) -> tuple[str, dict[str, Any] | None]:
    task_root = f"{remote_root}/{task.task_id}"
    output = ssh(
        task.worker,
        f"if test -f {shlex.quote(task_root + '/microcell-status.json')}; then "
        f"printf 'terminal\\n'; cat {shlex.quote(task_root + '/microcell-status.json')}; "
        f"elif test -f {shlex.quote(task_root + '/preliminary-status.json')}; then "
        f"printf 'preliminary\\n'; cat {shlex.quote(task_root + '/preliminary-status.json')}; "
        "else printf 'running\\n'; fi",
    )
    label, _, payload = output.partition("\n")
    return label.strip(), json.loads(payload) if payload.strip() else None


def launch_task(
    task: Task,
    *,
    commit: str,
    plan: dict[str, Any],
    results_root: Path,
    remote_worktree: str,
    remote_root: str,
) -> dict[str, Any]:
    descriptor = results_root / "dispatch" / f"{task.task_id}.json"
    atomic(descriptor, {
        "schema_version": 1,
        "experiment": plan["experiment"],
        "git_commit": commit,
        "dispatched_at": now(),
        "worker": task.worker,
        "task": asdict(task),
        "resources": plan["resources"],
    })
    remote_dispatch = f"{remote_root}/dispatch/{task.task_id}.json"
    task_root = f"{remote_root}/{task.task_id}"
    ssh(task.worker, f"mkdir -p {shlex.quote(remote_root + '/dispatch')}")
    run([
        "scp", "-q", "-o", "BatchMode=yes", str(descriptor),
        f"{task.worker}:{remote_dispatch}",
    ])
    command = (
        f"{shlex.quote(remote_worktree + '/.venv/bin/python')} "
        f"{shlex.quote(remote_worktree + '/scripts/launch_online_microcell.py')} "
        f"--worktree {shlex.quote(remote_worktree)} "
        f"--descriptor {shlex.quote(remote_dispatch)} "
        f"--task-root {shlex.quote(task_root)}"
    )
    output = ssh(task.worker, command)
    return json.loads(output.strip().splitlines()[-1])


def collect_task(task: Task, *, results_root: Path, remote_root: str) -> None:
    destination = results_root / "tasks" / task.task_id
    destination.parent.mkdir(parents=True, exist_ok=True)
    run([
        "rsync", "-a", "--partial", "-e", "ssh -o BatchMode=yes",
        f"{task.worker}:{remote_root}/{task.task_id}/", f"{destination}/",
    ])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--results-root", type=Path, required=True)
    parser.add_argument("--remote-worktree", required=True)
    parser.add_argument("--remote-root", required=True)
    parser.add_argument("--confirm-paid-launch")
    parser.add_argument("--poll-seconds", type=float, default=5)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    plan = json.loads(args.plan.read_text())
    tasks = build_tasks(plan)
    validate_plan(plan, tasks, args.commit)
    if args.check:
        print(json.dumps({
            "check": "passed",
            "blocks": len({task.block_id for task in tasks}),
            "cells": len(tasks),
            "workers": sorted({task.worker for task in tasks}),
        }, sort_keys=True))
        return 0
    if args.confirm_paid_launch != CONFIRMATION:
        raise SystemExit(f"confirmation required: {CONFIRMATION}")

    state_path = args.state.resolve()
    results_root = args.results_root.resolve()
    queue = [asdict(task) for task in tasks]
    by_id = {task.task_id: task for task in tasks}
    if state_path.exists():
        state = json.loads(state_path.read_text())
        if state.get("git_commit") != args.commit or state.get("queue") != queue:
            raise ValueError("resume state differs from the frozen Stage 3 queue")
        if any(cell["status"] == "dispatching" for cell in state["tasks"].values()):
            raise ValueError("a dispatch has unknown completion; reconcile manually")
    else:
        state = {
            "schema_version": 1,
            "experiment": plan["experiment"],
            "git_commit": args.commit,
            "created_at": now(),
            "updated_at": now(),
            "phase": "running",
            "queue": queue,
            "tasks": {task.task_id: {"status": "pending"} for task in tasks},
        }
        atomic(state_path, state)

    while True:
        changed = False
        for task_id, cell in state["tasks"].items():
            if cell["status"] != "running":
                continue
            task = by_id[task_id]
            label, payload = remote_status(task, args.remote_root)
            if label == "preliminary" and not cell.get("preliminary"):
                cell["preliminary"] = payload
                cell["preliminary_observed_at"] = now()
                changed = True
                print(json.dumps({"event": "preliminary", "task": task_id, **(payload or {})}), flush=True)
            elif label == "terminal":
                collect_task(task, results_root=results_root, remote_root=args.remote_root)
                artifact_ok = bool(payload and payload.get("result_artifact_count") == 1)
                cell.update({
                    "status": "complete" if artifact_ok else "exited_incomplete",
                    "terminal": payload,
                    "finished_at": now(),
                    "local_root": str(results_root / "tasks" / task_id),
                })
                changed = True
                print(json.dumps({"event": "terminal", "task": task_id, **(payload or {})}), flush=True)

        for group in range(len(plan["worker_groups"])):
            group_tasks = [task for task in tasks if task.group == group]
            active = any(state["tasks"][task.task_id]["status"] in {"dispatching", "running"}
                         for task in group_tasks)
            if active:
                continue
            pending_blocks = []
            for task in group_tasks:
                if state["tasks"][task.task_id]["status"] == "pending" and task.block_id not in pending_blocks:
                    pending_blocks.append(task.block_id)
            if not pending_blocks:
                continue
            block_id = pending_blocks[0]
            block = [task for task in group_tasks if task.block_id == block_id]
            for task in block:
                state["tasks"][task.task_id] = {
                    "status": "dispatching", "worker": task.worker, "at": now(),
                }
                state["updated_at"] = now()
                atomic(state_path, state)
                launch = launch_task(
                    task,
                    commit=args.commit,
                    plan=plan,
                    results_root=results_root,
                    remote_worktree=args.remote_worktree,
                    remote_root=args.remote_root,
                )
                state["tasks"][task.task_id].update({
                    "status": "running", "pid": launch["pid"], "task_root": launch["task_root"],
                })
                state["updated_at"] = now()
                atomic(state_path, state)
                print(json.dumps({"event": "launched", "task": task.task_id,
                                  "worker": task.worker, "block": block_id}), flush=True)
            changed = True

        statuses = [cell["status"] for cell in state["tasks"].values()]
        if all(status in {"complete", "exited_incomplete"} for status in statuses):
            state["phase"] = "collected" if all(status == "complete" for status in statuses) else "incomplete"
            state["updated_at"] = now()
            atomic(state_path, state)
            return 0 if state["phase"] == "collected" else 4
        if changed:
            state["updated_at"] = now()
            atomic(state_path, state)
        time.sleep(max(1, args.poll_seconds))


if __name__ == "__main__":
    raise SystemExit(main())
