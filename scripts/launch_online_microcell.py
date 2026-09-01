#!/usr/bin/env python3
"""Launch one bounded online-development microcell with durable artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


STRATEGIES = {
    "c0": "none",
    "c1": "reciprocal-once-v1",
    "c2": "reciprocal-every-eligible-v1",
}
LEAN_IMAGE = (
    "ghcr.io/verifiedmechanisms/re-takehome-lean"
    "@sha256:ee48287cd31c0a7df572093a879ed7289c2f01fec6c7af8716c605fc8c670c39"
)


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def execute(worktree: Path, descriptor_path: Path, task_root: Path) -> int:
    descriptor = json.loads(descriptor_path.read_text())
    task = descriptor["task"]
    condition = task["condition"]
    if condition not in STRATEGIES or task["strategy"] != STRATEGIES[condition]:
        raise ValueError("condition/strategy pair is not an unchanged v2 arm")
    problem = task["problem"]
    source = worktree / "sample-problems" / problem
    sample_manifest = worktree / "sample-problems" / "manifest.json"
    manifest = json.loads(sample_manifest.read_text())
    entry = next(item for item in manifest["problems"] if item["id"] == problem)
    problem_set = task_root / "problem-set"
    (problem_set / problem).mkdir(parents=True, exist_ok=False)
    shutil.copy2(source / "challenge.lean", problem_set / problem / "challenge.lean")
    shutil.copy2(source / "problem.md", problem_set / problem / "problem.md")
    atomic(problem_set / "manifest.json", {
        "schema_version": 1,
        "set": task["task_id"],
        "problems": [entry],
    })

    resources = descriptor["resources"]
    output = task_root / "outputs"
    argv = [
        str(worktree / ".venv/bin/python"), str(worktree / "run.py"),
        "--problems", str(problem_set), "--out", str(output),
        "--n-workers", "1", "--agent", "collaboration_engine_v2.agent:create_agent",
    ]
    atomic(task_root / "provenance.json", {
        "schema_version": 1,
        "experiment": "online-development-v1-stage2",
        "task": task,
        "git_commit": descriptor["git_commit"],
        "dispatched_at": descriptor["dispatched_at"],
        "worker": descriptor["worker"],
        "resources": resources,
        "sample_manifest_sha256": sha256(sample_manifest),
        "agent_sha256": sha256(worktree / "collaboration_engine_v2" / "agent.py"),
        "strategies_sha256": sha256(worktree / "collaboration_engine_v2" / "strategies.py"),
        "lean_image": LEAN_IMAGE,
        "command": argv,
    })
    environment = dict(os.environ)
    environment.update({
        # Shared remote virtual environments may contain editable-install
        # pointers to an older checkout. The frozen task worktree must win.
        "PYTHONPATH": os.pathsep.join([str(worktree / "src"), str(worktree)]),
        "LEAN_IMAGE": LEAN_IMAGE,
        "VM_TIME_LIMIT_S": str(resources["outer_time_s"]),
        "VM_VERIFY_RESERVE_S": str(resources["verify_reserve_s"]),
        "VM_BUDGET_USD": str(resources["budget_usd"]),
        "LEAN_CHECK_TIMEOUT_S": str(resources["lean_check_timeout_s"]),
        "COMPARATOR_TIMEOUT_S": str(resources["comparator_timeout_s"]),
        "COLLAB_DESIGN_ID": "collaboration-engine-v2",
        "COLLAB_CONDITION": condition,
        "COLLAB_STRATEGY": task["strategy"],
        "COLLAB_SEED": str(task["seed"]),
        "COLLAB_MAX_CALLS_PER_MODEL": str(resources["max_calls_per_model"]),
        "COLLAB_GENERATION_MAX_TOKENS": str(resources["generation_max_tokens"]),
        "COLLAB_TEMPERATURE": str(resources["temperature"]),
        "COLLAB_MAX_RESTARTS": str(resources["max_restarts"]),
        "COLLAB_DIAGNOSTIC_CHARS": str(resources["diagnostic_chars"]),
        "COLLAB_FAILURE_MEMORY_CHARS": str(resources["failure_memory_chars"]),
        "COLLAB_PEER_PACKET_CHARS": str(resources["peer_packet_chars"]),
        "COLLAB_DISPATCH_CUTOFF_S": str(resources["dispatch_cutoff_s"]),
        "COLLAB_MAX_FREE_429_RETRIES": str(resources["max_cost_free_429_retries"]),
    })
    with (task_root / "run.log").open("ab", buffering=0) as log:
        process = subprocess.run(
            argv, cwd=worktree, env=environment,
            stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
        )
    atomic(task_root / "microcell-status.json", {
        "schema_version": 1,
        "task_id": task["task_id"],
        "exit_code": process.returncode,
        "finished_at": now(),
    })
    return process.returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worktree", type=Path, required=True)
    parser.add_argument("--descriptor", type=Path, required=True)
    parser.add_argument("--task-root", type=Path, required=True)
    parser.add_argument("--execute", action="store_true")
    args = parser.parse_args()
    worktree = args.worktree.resolve()
    descriptor = args.descriptor.resolve()
    task_root = args.task_root.resolve()
    if args.execute:
        try:
            return execute(worktree, descriptor, task_root)
        except BaseException as exc:
            atomic(task_root / "microcell-status.json", {
                "schema_version": 1,
                "task_id": task_root.name,
                "exit_code": 255,
                "finished_at": now(),
                "error": f"{type(exc).__name__}: {exc}",
            })
            return 255
    if task_root.exists():
        raise SystemExit("task root already exists")
    task_root.parent.mkdir(parents=True, exist_ok=True)
    task_root.mkdir()
    command = [
        str(worktree / ".venv/bin/python"), str(Path(__file__).resolve()),
        "--worktree", str(worktree), "--descriptor", str(descriptor),
        "--task-root", str(task_root), "--execute",
    ]
    with (task_root / "launcher.log").open("ab", buffering=0) as log:
        process = subprocess.Popen(
            command, cwd=worktree, stdin=subprocess.DEVNULL,
            stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
        )
    atomic(task_root / "microcell-launch.json", {
        "schema_version": 1,
        "pid": process.pid,
        "launched_at": now(),
        "command": command,
    })
    print(json.dumps({"pid": process.pid, "task_root": str(task_root)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
