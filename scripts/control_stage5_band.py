#!/usr/bin/env python3
"""Availability-aware, fixed-order dispatcher for the final Wave D matrix."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


WORKERS = [f"takehome-worker-{index}" for index in range(1, 9)]
REMOTE_WORKTREE = Path("/opt/sfrv2-stage5-band4-d43af01-20260903/checkout")
REMOTE_ROOT = Path("/opt/salvage-fill-reserve-v2-stage5-band4-v1-20260903")
DISPATCH_CUTOFF = datetime.fromisoformat("2026-09-03T11:59:00+00:00")


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def atomic(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def remote(worker: str, command: str, *, check: bool = True) -> str:
    completed = subprocess.run(
        ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=8", worker, command],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    if check and completed.returncode:
        raise RuntimeError(
            f"{worker} command failed ({completed.returncode}): {completed.stderr.strip()}"
        )
    return completed.stdout


def worker_is_free(worker: str) -> bool:
    command = (
        "if pgrep -af '[l]aunch_online_microcell.py|[r]un.py' >/dev/null "
        "|| test -n \"$(docker ps -q 2>/dev/null)\"; then exit 3; else exit 0; fi"
    )
    completed = subprocess.run(
        ["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=8", worker, command],
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    )
    return completed.returncode == 0


def load_blocks(order_path: Path) -> list[list[dict[str, Any]]]:
    entries = json.loads(order_path.read_text())["entries"]
    blocks: list[list[dict[str, Any]]] = []
    for entry in entries:
        if not blocks or blocks[-1][0]["block_id"] != entry["block_id"]:
            blocks.append([])
        blocks[-1].append(entry)
    if [len(block) for block in blocks] != [2] + [4] * 24:
        raise ValueError("dispatch order is not one two-cell preflight plus 24 four-arm blocks")
    return blocks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=Path, required=True)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--pause-file", type=Path, required=True)
    parser.add_argument("--poll-seconds", type=float, default=10)
    args = parser.parse_args()
    blocks = load_blocks(args.order.resolve())

    if args.state.exists():
        state = json.loads(args.state.read_text())
        if state["task_ids"] != [entry["task_id"] for block in blocks for entry in block]:
            raise ValueError("existing controller state does not match frozen order")
    else:
        state = {
            "schema_version": 1,
            "experiment": "salvage-fill-reserve-v2-stage5-band-v1",
            "created_at": now(),
            "updated_at": now(),
            "phase": "running",
            "task_ids": [entry["task_id"] for block in blocks for entry in block],
            "cells": {
                entry["task_id"]: {"status": "pending", "block_id": entry["block_id"]}
                for block in blocks for entry in block
            },
        }
        atomic(args.state, state)

    while True:
        # Reconcile only launches recorded by this controller. No paid cell is retried.
        for task_id, cell in state["cells"].items():
            if cell["status"] != "running":
                continue
            status_path = REMOTE_ROOT / "tasks" / task_id / "microcell-status.json"
            output = remote(
                cell["worker"],
                f"test -f {status_path} && cat {status_path}",
                check=False,
            )
            if output.strip():
                terminal = json.loads(output)
                cell.update({"status": "terminal", "finished_at": now(), "terminal": terminal})

        terminal_blocks = 0
        incomplete_blocks = 0
        next_block: list[dict[str, Any]] | None = None
        for block in blocks:
            statuses = [state["cells"][entry["task_id"]]["status"] for entry in block]
            if all(status == "terminal" for status in statuses):
                terminal_blocks += 1
            elif any(status in {"dispatching", "running", "terminal"} for status in statuses):
                incomplete_blocks += 1
            elif next_block is None:
                next_block = block

        if terminal_blocks == len(blocks):
            state["phase"] = "complete"
            state["completed_at"] = now()
            state["updated_at"] = now()
            atomic(args.state, state)
            return 0

        may_dispatch = (
            next_block is not None
            and incomplete_blocks < 2
            and not args.pause_file.exists()
            and datetime.now(timezone.utc) < DISPATCH_CUTOFF
        )
        if may_dispatch:
            assigned_running = {
                cell.get("worker") for cell in state["cells"].values()
                if cell["status"] in {"dispatching", "running"}
            }
            candidates = [worker for worker in WORKERS if worker not in assigned_running]
            free = [worker for worker in candidates if worker_is_free(worker)]
            if len(free) >= len(next_block):
                for entry, worker in zip(next_block, free, strict=False):
                    task_id = entry["task_id"]
                    cell = state["cells"][task_id]
                    descriptor = json.loads(Path(entry["descriptor"]).read_text())
                    descriptor["worker"] = worker
                    descriptor["dispatched_at"] = now()
                    cell.update({"status": "dispatching", "worker": worker, "at": now()})
                    state["updated_at"] = now()
                    atomic(args.state, state)
                    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as handle:
                        json.dump(descriptor, handle, indent=2, sort_keys=True)
                        handle.write("\n")
                        temporary = Path(handle.name)
                    remote_descriptor = REMOTE_ROOT / "runtime-dispatch" / temporary.name
                    subprocess.run(
                        ["ssh", worker, "mkdir", "-p", str(remote_descriptor.parent)], check=True
                    )
                    subprocess.run(
                        ["scp", "-q", str(temporary), f"{worker}:{remote_descriptor}"], check=True
                    )
                    temporary.unlink()
                    task_root = REMOTE_ROOT / "tasks" / task_id
                    output = remote(
                        worker,
                        f"test ! -e {task_root} && {REMOTE_WORKTREE}/.venv/bin/python "
                        f"{REMOTE_WORKTREE}/scripts/launch_online_microcell.py "
                        f"--worktree {REMOTE_WORKTREE} --descriptor {remote_descriptor} "
                        f"--task-root {task_root}",
                    )
                    launch = json.loads(output.strip().splitlines()[-1])
                    cell.update({"status": "running", "pid": launch["pid"], "launched_at": now()})
                    state["updated_at"] = now()
                    atomic(args.state, state)

        state["updated_at"] = now()
        atomic(args.state, state)
        time.sleep(max(2, args.poll_seconds))


if __name__ == "__main__":
    raise SystemExit(main())
