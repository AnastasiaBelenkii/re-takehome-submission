#!/usr/bin/env python3
"""Collect and push the Stage 6 expanded-band confirmation wave."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import time
from collections import Counter
from datetime import datetime, time as clock_time
from pathlib import Path
from zoneinfo import ZoneInfo

ROOT = Path(os.environ.get("STAGE6_PUSH_REPO", "/opt/stage6-pusher/repo"))
ARCHIVE = ROOT / "evidence/archives/stage6-confirm-20260903"
LOG = ROOT / "experiments/stage6-expanded/LOG.md"
REMOTE = "/opt/stage6-confirm-20260903/global"
SOLO_REMOTE = "/opt/stage6-confirm-20260903/solo-global"
HOSTS = ("marketplace", "worker2", "worker3", "worker4", "worker5", "worker6", "worker7", "worker8", "worker10")
TARGETS = {
    "marketplace": None,
    "worker2": "root@10.122.0.4", "worker3": "root@10.122.0.3",
    "worker4": "root@10.122.0.5", "worker5": "root@10.122.0.7",
    "worker6": "root@10.122.0.6", "worker7": "root@10.122.0.8",
    "worker8": "root@10.122.0.10", "worker10": "root@10.122.0.11",
}
KEEP = ("result.json", "events.jsonl", "transcript.json", "solution.lean", "preliminary-status.json", "provenance.json", "queue-state.json")
PT = ZoneInfo("America/Los_Angeles")
ARMS = ("qwen-solo-plus", "gptoss-solo-plus", "c0plus-reserve", "c1plus-fill-reserve")


def now_pt() -> datetime:
    return datetime.now(PT)


def stamp() -> str:
    return now_pt().strftime("%H:%M PT")


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(("git", *args), cwd=ROOT, text=True, capture_output=True, check=check)


def append_log(line: str) -> None:
    with LOG.open("a") as handle:
        handle.write(f"- {stamp()} — {line}\n")


def collect() -> tuple[list[dict], dict]:
    ARCHIVE.mkdir(parents=True, exist_ok=True)
    for host in HOSTS:
        number = 1 if host == "marketplace" else int(host.removeprefix("worker"))
        destination = ARCHIVE / "hosts" / f"takehome-worker-{number}" / "cells"
        destination.mkdir(parents=True, exist_ok=True)
        command = ["rsync", "-a", "--timeout=30", "--include=*/"]
        command.extend(f"--include={name}" for name in KEEP)
        target = TARGETS[host]
        for remote_root in (REMOTE, SOLO_REMOTE):
            source = f"{remote_root}/{host}/cells/"
            source_path = Path(source)
            if target is None and not source_path.exists():
                continue
            this_command = list(command)
            this_command.extend(("--exclude=*", source if target is None else f"{target}:{source}", f"{destination}/"))
            subprocess.run(this_command, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    source = Path(f"{REMOTE}/global-controller-state.json")
    if source.exists():
        shutil.copy2(source, ARCHIVE / "global-controller-state.json")
    solo_source = Path(f"{SOLO_REMOTE}/global-controller-state.json")
    if solo_source.exists():
        shutil.copy2(solo_source, ARCHIVE / "solo-global-controller-state.json")
    state_path = ARCHIVE / "global-controller-state.json"
    state = json.loads(state_path.read_text()) if state_path.exists() else {}
    results = []
    for path in ARCHIVE.rglob("result.json"):
        try:
            value = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if value.get("problem_id"):
            results.append(value)
    return results, state


def read_state(path: str) -> dict:
    state_path = Path(path) / "global-controller-state.json"
    if not state_path.exists():
        return {}
    try:
        return json.loads(state_path.read_text())
    except (OSError, json.JSONDecodeError):
        return {}


def counts(results: list[dict]) -> tuple[Counter, Counter]:
    passed, totals = Counter(), Counter()
    for result in results:
        arm = str((result.get("agent_metadata") or {}).get("condition", "unknown"))
        totals[arm] += 1
        passed[arm] += int(bool(result.get("passed")))
    return passed, totals


def push(results: list[dict]) -> None:
    passed, totals = counts(results)
    arms = ", ".join(f"{arm} {passed[arm]}/{totals[arm]}" for arm in ARMS)
    message = f"Archive root evidence/archives/stage6-confirm-20260903; {len(results)} cells; passes per arm: {arms}"
    append_log("PUSH: " + message)
    git("add", "evidence/archives/stage6-confirm-20260903", "experiments/stage6-expanded/LOG.md")
    if git("diff", "--cached", "--quiet", check=False).returncode:
        git("commit", "-m", message)
        git("push", "origin", "HEAD:evidence/results-20260902")


def main() -> int:
    time.sleep(30)
    last_push = 0.0
    while True:
        results, state = collect()
        statuses = Counter(item.get("status", "unknown") for item in state.get("tasks", {}).values())
        terminal = statuses["complete"] + statuses["exited_incomplete"]
        running = statuses["running"] + statuses["dispatching"]
        queued = statuses["pending"]
        passed, totals = counts(results)
        log_text = LOG.read_text() if LOG.exists() else ""
        changed = False
        if queued == 0 and "solo extension launched" not in log_text and "solo extension skipped:" not in log_text:
            if now_pt().time() < clock_time(23, 0):
                launch = subprocess.run(
                    ("sh", str(ROOT / "scripts/launch_stage6_solo_extension.sh")),
                    cwd=ROOT, text=True, capture_output=True,
                )
                if launch.returncode != 0:
                    append_log(f"solo extension launch failed before dispatch: {launch.stderr.strip()}")
                    changed = True
                log_text = LOG.read_text() if LOG.exists() else log_text
        for when in (clock_time(21, 30), clock_time(22, 30), clock_time(23, 30), clock_time(0, 30)):
            marker = when.strftime("%H:%M PT confirm status")
            due = now_pt().time() >= when if when.hour else now_pt().time() < clock_time(12, 0) and now_pt().time() >= when
            if due and marker not in log_text:
                arm_text = ", ".join(f"{arm} {passed[arm]}/{totals[arm]}" for arm in ARMS)
                append_log(f"{marker} — terminal {terminal} / running {running} / queued {queued}; passes {arm_text}.")
                log_text += marker
                changed = True
        if now_pt().time() >= clock_time(23, 0) and "solo extension launched" not in log_text and "solo extension skipped:" not in log_text:
            append_log("solo extension skipped: not all 128 primary cells had dispatched by the 23:00 PT cutoff.")
            log_text += "solo extension skipped:"
            changed = True
        if state.get("phase") == "complete" and "confirm complete," not in log_text:
            append_log(f"confirm complete, {terminal} cells terminal; replay gate ready.")
            changed = True
        if changed or time.monotonic() - last_push >= 1800:
            push(results)
            last_push = time.monotonic()
        time.sleep(60)


if __name__ == "__main__":
    raise SystemExit(main())
