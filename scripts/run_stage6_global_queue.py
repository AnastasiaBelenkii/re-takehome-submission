#!/usr/bin/env python3
"""Durable global FIFO dispatcher for Stage 6 worker microcells.

The controller runs on worker 1.  It assigns the next undispatched descriptor
to each available worker, while each paid cell itself runs in a worker-local
tmux session.  State is persisted before and after every dispatch so a cell is
never silently retried.
"""

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


SSH_TARGETS = {
    "marketplace": "localhost",
    "worker2": "root@10.122.0.4",
    "worker3": "root@10.122.0.3",
    "worker4": "root@10.122.0.5",
    "worker5": "root@10.122.0.7",
    "worker6": "root@10.122.0.6",
    "worker7": "root@10.122.0.8",
    "worker8": "root@10.122.0.10",
    "worker10": "root@10.122.0.11",
}
SSH_OPTIONS = (
    "-o", "ConnectTimeout=10",
    "-o", "ControlMaster=auto",
    "-o", "ControlPath=/tmp/stage6-global-%C",
    "-o", "ControlPersist=600",
)


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def atomic(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def run(*command: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, text=True, capture_output=True, check=check)


def ssh(host: str, command: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return run("ssh", *SSH_OPTIONS, SSH_TARGETS.get(host, host), command, check=check)


def retry_prelaunch(command: tuple[str, ...], attempts: int = 12) -> subprocess.CompletedProcess[str]:
    """Retry only idempotent work that occurs before any paid-cell launch."""
    last: subprocess.CompletedProcess[str] | None = None
    for attempt in range(attempts):
        last = run(*command, check=False)
        if last.returncode == 0:
            return last
        time.sleep(min(10, 1 + attempt))
    assert last is not None
    raise RuntimeError(f"pre-launch transport failed after {attempts} tries: {command}: {last.stderr}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--queue", type=Path, required=True)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--remote-root", required=True)
    parser.add_argument("--runtime", required=True)
    parser.add_argument(
        "--runtime-by-condition",
        help="JSON object mapping task conditions to worker-local runtime paths",
    )
    parser.add_argument("--session", required=True)
    parser.add_argument("--launch-deadline", help="optional per-cell dispatch deadline")
    parser.add_argument("--hosts", nargs="+", required=True)
    parser.add_argument("--poll-seconds", type=float, default=5)
    args = parser.parse_args()
    runtime_by_condition = json.loads(args.runtime_by_condition) if args.runtime_by_condition else {}

    deadline = datetime.fromisoformat(args.launch_deadline) if args.launch_deadline else None
    queue = json.loads(args.queue.read_text())
    descriptor_paths = [Path(item) for item in queue["descriptors"]]
    descriptors = [json.loads(path.read_text()) for path in descriptor_paths]
    descriptors.sort(key=lambda item: int(item["task"]["dispatch_index"]))
    task_ids = [item["task"]["task_id"] for item in descriptors]
    if len(task_ids) != len(set(task_ids)):
        raise ValueError("duplicate task IDs")

    if args.state.exists():
        state = json.loads(args.state.read_text())
        if state["task_ids"] != task_ids:
            raise ValueError("persisted state differs from frozen global queue")
        if any(item["status"] == "dispatching" for item in state["tasks"].values()):
            raise RuntimeError("ambiguous prior dispatch; refusing to retry")
        state["hosts"] = args.hosts
        state["updated_at"] = now()
        atomic(args.state, state)
    else:
        state = {
            "schema_version": 1,
            "experiment": queue["experiment"],
            "created_at": now(),
            "updated_at": now(),
            "phase": "running",
            "hosts": args.hosts,
            "task_ids": task_ids,
            "tasks": {task_id: {"status": "pending"} for task_id in task_ids},
        }
        atomic(args.state, state)

    active: dict[str, str] = {}
    for task_id, item in state["tasks"].items():
        if item["status"] == "running":
            active[item["worker_host"]] = task_id

    while True:
        # Adopt completed worker-local one-cell queues.
        for host, task_id in list(active.items()):
            state_path = f"{args.remote_root}/{host}/cells/{task_id}/queue-state.json"
            result = ssh(host, f"test -f {shlex.quote(state_path)} && jq -c . {shlex.quote(state_path)}", check=False)
            if result.returncode != 0 or not result.stdout.strip():
                continue
            remote_state = json.loads(result.stdout)
            if remote_state.get("phase") == "running":
                continue
            cell = remote_state.get("tasks", {}).get(task_id, {})
            status = cell.get("status", "exited_incomplete")
            state["tasks"][task_id].update({
                "status": "complete" if status == "complete" else "exited_incomplete",
                "finished_at": now(),
                "terminal": cell.get("terminal"),
            })
            del active[host]
            state["updated_at"] = now()
            atomic(args.state, state)

        pending = [task_id for task_id in task_ids if state["tasks"][task_id]["status"] == "pending"]
        if not pending and not active:
            state["phase"] = (
                "complete" if all(item["status"] == "complete" for item in state["tasks"].values())
                else "incomplete"
            )
            state["updated_at"] = now()
            atomic(args.state, state)
            return 0 if state["phase"] == "complete" else 4

        if deadline is not None and datetime.now(timezone.utc) >= deadline and pending:
            for task_id in pending:
                state["tasks"][task_id] = {"status": "skipped_deadline", "at": now()}
            state["phase"] = "draining"
            state["updated_at"] = now()
            atomic(args.state, state)
            pending = []

        # Dispatch strictly from the head of the global queue.
        for host in args.hosts:
            if not pending or host in active:
                continue
            # Do not overlap the calibration's one remaining paid cell.
            calibration = ssh(
                host,
                f"test -f /opt/stage6-calibration-20260903/{host.replace('marketplace', 'worker1')}/queue-state.json "
                f"&& jq -r .phase /opt/stage6-calibration-20260903/{host.replace('marketplace', 'worker1')}/queue-state.json",
                check=False,
            )
            if calibration.returncode == 0 and calibration.stdout.strip() == "running":
                continue
            if ssh(host, f"tmux has-session -t {shlex.quote(args.session)}", check=False).returncode == 0:
                continue

            task_id = pending.pop(0)
            index = task_ids.index(task_id)
            descriptor = json.loads(json.dumps(descriptors[index]))
            worker_number = 1 if host == "marketplace" else int(host.removeprefix("worker"))
            descriptor["worker"] = f"takehome-worker-{worker_number}"
            descriptor["task"]["executing_worker"] = f"takehome-worker-{worker_number}"
            descriptor["dispatched_at"] = now()

            dispatch_dir = args.state.parent / "runtime-dispatch"
            descriptor_file = dispatch_dir / f"{index:03d}-{task_id}.json"
            queue_file = dispatch_dir / f"{index:03d}-{task_id}-queue.json"
            remote_worker = f"{args.remote_root}/{host}/cells/{task_id}"
            atomic(descriptor_file, descriptor)
            atomic(queue_file, {
                "schema_version": 1,
                "experiment": queue["experiment"],
                "worker": f"takehome-worker-{worker_number}",
                "descriptors": [f"{remote_worker}/descriptor.json"],
            })

            state["tasks"][task_id].update({"status": "dispatching", "at": now(), "worker_host": host})
            state["updated_at"] = now()
            atomic(args.state, state)
            setup = (
                f"test ! -e {shlex.quote(remote_worker + '/tasks/' + task_id)} && "
                f"mkdir -p {shlex.quote(remote_worker)}"
            )
            target = SSH_TARGETS.get(host, host)
            retry_prelaunch(("ssh", *SSH_OPTIONS, target, setup))
            retry_prelaunch(("scp", "-q", *SSH_OPTIONS, str(descriptor_file), f"{target}:{remote_worker}/descriptor.json"))
            retry_prelaunch(("scp", "-q", *SSH_OPTIONS, str(queue_file), f"{target}:{remote_worker}/queue.json"))
            command = (
                f"cd {shlex.quote(runtime_by_condition.get(descriptor['task'].get('condition'), args.runtime))} && exec .venv/bin/python scripts/run_remote_microcell_queue.py "
                f"--worktree {shlex.quote(runtime_by_condition.get(descriptor['task'].get('condition'), args.runtime))} --queue {remote_worker}/queue.json "
                f"--run-root {remote_worker} >> {remote_worker}/queue.log 2>&1"
            )
            launch_command = f"tmux new-session -d -s {shlex.quote(args.session)} {shlex.quote(command)}"
            for attempt in range(12):
                launched = ssh(host, launch_command, check=False)
                if launched.returncode == 0:
                    break
                # A refused TCP connection proves the remote command was not
                # delivered, so retrying cannot duplicate a paid dispatch.
                if "Connection refused" not in launched.stderr:
                    raise RuntimeError(f"ambiguous dispatch of {task_id} to {host}: {launched.stderr}")
                time.sleep(min(10, 1 + attempt))
            else:
                raise RuntimeError(f"pre-dispatch connection refused for {task_id} on {host}")
            state["tasks"][task_id].update({"status": "running", "launched_at": now()})
            state["updated_at"] = now()
            atomic(args.state, state)
            active[host] = task_id

        time.sleep(max(1, args.poll_seconds))


if __name__ == "__main__":
    raise SystemExit(main())
