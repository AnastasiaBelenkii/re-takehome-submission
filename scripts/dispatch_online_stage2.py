#!/usr/bin/env python3
"""Dispatch and collect the frozen online-development stage-2 microcell plan."""

from __future__ import annotations

import argparse
import json
import shlex
import subprocess
from datetime import datetime, timezone
from pathlib import Path


CONFIRMATION = "I_UNDERSTAND_THIS_LAUNCHES_PAID_STAGE2_CELLS"


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def run(argv: list[str], *, capture: bool = False) -> str:
    result = subprocess.run(
        argv, check=True, text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
    )
    return result.stdout if capture else ""


def ssh(host: str, command: str) -> str:
    return run(
        ["ssh", "-o", "BatchMode=yes", host, "bash", "-lc", shlex.quote(command)],
        capture=True,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--local-root", type=Path, required=True)
    parser.add_argument("--remote-worktree", required=True)
    parser.add_argument("--remote-root", required=True)
    parser.add_argument("--confirm-paid-launch")
    parser.add_argument("--collect", action="store_true")
    args = parser.parse_args()
    plan = json.loads(args.plan.read_text())
    checkout_commit = run(["git", "rev-parse", "HEAD"], capture=True).strip()
    local_root = args.local_root.resolve()
    local_root.mkdir(parents=True, exist_ok=True)

    if args.collect:
        for task in plan["tasks"]:
            remote_task = f"{args.remote_root}/{task['task_id']}"
            status = ssh(
                task["worker"],
                f"test -f {shlex.quote(remote_task + '/microcell-status.json')} && "
                f"cat {shlex.quote(remote_task + '/microcell-status.json')} || true",
            )
            if not status.strip():
                print(json.dumps({"task_id": task["task_id"], "status": "running"}))
                continue
            destination = local_root / "tasks" / task["task_id"]
            destination.parent.mkdir(parents=True, exist_ok=True)
            run([
                "rsync", "-a", "--partial", "-e", "ssh -o BatchMode=yes",
                f"{task['worker']}:{remote_task}/", f"{destination}/",
            ])
            print(status.strip())
        return 0

    if args.confirm_paid_launch != CONFIRMATION:
        raise SystemExit(f"confirmation required: {CONFIRMATION}")
    for task in plan["tasks"]:
        descriptor = {
            "schema_version": 1,
            "git_commit": checkout_commit,
            "dispatched_at": now(),
            "worker": task["worker"],
            "task": {key: value for key, value in task.items() if key != "worker"},
            "resources": plan["resources"],
        }
        descriptor_path = local_root / "dispatch" / f"{task['task_id']}.json"
        descriptor_path.parent.mkdir(parents=True, exist_ok=True)
        descriptor_path.write_text(json.dumps(descriptor, indent=2) + "\n")
        remote_dispatch = f"{args.remote_root}/dispatch/{task['task_id']}.json"
        remote_task = f"{args.remote_root}/{task['task_id']}"
        ssh(task["worker"], f"mkdir -p {shlex.quote(args.remote_root + '/dispatch')}")
        run([
            "scp", "-q", "-o", "BatchMode=yes", str(descriptor_path),
            f"{task['worker']}:{remote_dispatch}",
        ])
        command = (
            f"{shlex.quote(args.remote_worktree + '/.venv/bin/python')} "
            f"{shlex.quote(args.remote_worktree + '/scripts/launch_online_microcell.py')} "
            f"--worktree {shlex.quote(args.remote_worktree)} "
            f"--descriptor {shlex.quote(remote_dispatch)} "
            f"--task-root {shlex.quote(remote_task)}"
        )
        output = ssh(task["worker"], command)
        print(output.strip())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
