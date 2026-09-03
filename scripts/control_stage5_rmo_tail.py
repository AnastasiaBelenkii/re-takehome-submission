#!/usr/bin/env python3
"""Dispatch the fixed rmo tail after the main Wave D dispatch cutoff."""

from __future__ import annotations

import argparse
import json
import subprocess
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

from control_stage5_band import atomic, now, remote, worker_is_free


WORKERS = [f"takehome-worker-{index}" for index in range(1, 9)]
REMOTE_WORKTREE = Path("/opt/sfrv2-importfix-853884e-stage5-tail-20260903/checkout")
REMOTE_ROOT = Path("/opt/salvage-fill-reserve-v2-stage5-rmo-tail-v1-20260903")
START = datetime.fromisoformat("2026-09-03T09:30:00+00:00")
STOP = datetime.fromisoformat("2026-09-03T11:59:00+00:00")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=Path, required=True)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--poll-seconds", type=float, default=8)
    args = parser.parse_args()

    entries = json.loads(args.order.resolve().read_text())["entries"]
    blocks = [entries[index:index + 4] for index in range(0, len(entries), 4)]
    if len(entries) != 24 or any(len(block) != 4 for block in blocks):
        raise ValueError("rmo tail must be six adjacent four-arm blocks")

    task_ids = [entry["task_id"] for entry in entries]
    if args.state.exists():
        state = json.loads(args.state.read_text())
        if state["task_ids"] != task_ids:
            raise ValueError("existing tail state does not match frozen order")
    else:
        state = {
            "schema_version": 1,
            "experiment": "salvage-fill-reserve-v2-stage5-rmo-tail-v1",
            "created_at": now(),
            "updated_at": now(),
            "phase": "waiting_for_0230_pt",
            "task_ids": task_ids,
            "cells": {
                entry["task_id"]: {
                    "status": "pending", "block_id": entry["block_id"]
                } for entry in entries
            },
        }
        atomic(args.state, state)

    while True:
        for task_id, cell in state["cells"].items():
            if cell["status"] != "running":
                continue
            status_path = REMOTE_ROOT / "tasks" / task_id / "microcell-status.json"
            output = remote(
                cell["worker"], f"test -f {status_path} && cat {status_path}", check=False
            )
            if output.strip():
                cell.update({"status": "terminal", "finished_at": now(),
                             "terminal": json.loads(output)})

        if all(cell["status"] == "terminal" for cell in state["cells"].values()):
            state.update({"phase": "complete", "completed_at": now(), "updated_at": now()})
            atomic(args.state, state)
            return 0

        current = datetime.now(timezone.utc)
        state["phase"] = "waiting_for_0230_pt" if current < START else "running"
        incomplete = 0
        next_block = None
        for block in blocks:
            statuses = [state["cells"][entry["task_id"]]["status"] for entry in block]
            if any(status in {"dispatching", "running", "terminal"} for status in statuses) \
                    and not all(status == "terminal" for status in statuses):
                incomplete += 1
            elif all(status == "pending" for status in statuses) and next_block is None:
                next_block = block

        if START <= current < STOP and next_block is not None and incomplete < 2:
            assigned = {
                cell.get("worker") for cell in state["cells"].values()
                if cell["status"] in {"dispatching", "running"}
            }
            free = [worker for worker in WORKERS
                    if worker not in assigned and worker_is_free(worker)]
            if len(free) >= 4:
                for entry, worker in zip(next_block, free, strict=False):
                    task_id = entry["task_id"]
                    descriptor = json.loads(Path(entry["descriptor"]).read_text())
                    descriptor.update({"worker": worker, "dispatched_at": now()})
                    cell = state["cells"][task_id]
                    cell.update({"status": "dispatching", "worker": worker, "at": now()})
                    state["updated_at"] = now()
                    atomic(args.state, state)
                    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as handle:
                        json.dump(descriptor, handle, indent=2, sort_keys=True)
                        handle.write("\n")
                        temporary = Path(handle.name)
                    remote_descriptor = REMOTE_ROOT / "runtime-dispatch" / temporary.name
                    subprocess.run(["ssh", worker, "mkdir", "-p",
                                    str(remote_descriptor.parent)], check=True)
                    subprocess.run(["scp", "-q", str(temporary),
                                    f"{worker}:{remote_descriptor}"], check=True)
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
                    cell.update({"status": "running", "pid": launch["pid"],
                                 "launched_at": now()})

        state["updated_at"] = now()
        atomic(args.state, state)
        time.sleep(max(2, args.poll_seconds))


if __name__ == "__main__":
    raise SystemExit(main())
