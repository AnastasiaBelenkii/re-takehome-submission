#!/usr/bin/env python3
"""Collect and push the Stage 6 expanded-band confirmation wave."""

from __future__ import annotations

import json
import csv
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
QQ_REMOTE = "/opt/stage6-confirm-20260903/qq-global"
REPLAY_REMOTE = "/opt/stage6-confirm-replay-20260903"
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
ARMS = ("qwen-solo-plus", "gptoss-solo-plus", "c0plus-reserve", "c1plus-fill-reserve", "c0-qq")


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
        for remote_root in (REMOTE, SOLO_REMOTE, QQ_REMOTE):
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
    qq_source = Path(f"{QQ_REMOTE}/global-controller-state.json")
    if qq_source.exists():
        shutil.copy2(qq_source, ARCHIVE / "qq-global-controller-state.json")
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


def state_counts(state: dict) -> tuple[int, int, int]:
    statuses = Counter(item.get("status", "unknown") for item in state.get("tasks", {}).values())
    return (
        statuses["complete"] + statuses["exited_incomplete"],
        statuses["running"] + statuses["dispatching"],
        statuses["pending"],
    )


def maybe_finish_replay(log_text: str) -> bool:
    if (
        "confirm replay launched" not in log_text
        or "confirm replay pushed:" in log_text
        or "confirm replay skipped remaining" in log_text
    ):
        return False
    local = Path("/opt/stage6-pusher/confirm-replay")
    local.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        ("rsync", "-a", "--timeout=30", f"worker9:{REPLAY_REMOTE}/output/", f"{local}/"),
        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
    )
    result_path = local / "result.json"
    if not result_path.exists():
        return False
    result = json.loads(result_path.read_text())
    if result.get("status") not in {"complete", "budget_cap"}:
        return False
    rows: list[dict[str, str]] = []
    with (local / "packet-replay.csv").open(newline="") as handle:
        rows = list(csv.DictReader(handle))
    destination = ROOT / "experiments/analysis/packet-replay-confirm.csv"
    shutil.copy2(local / "packet-replay.csv", destination)
    sources = len({row["source_call_id"] for row in rows})
    with_rows = [row for row in rows if row["variant"] == "with_packet"]
    without_rows = [row for row in rows if row["variant"] == "without_packet"]
    warm = lambda values: sum(
        row.get("warm_accepted", "").lower() == "true" and not row.get("error")
        for row in values
    )
    wp, wop = warm(with_rows), warm(without_rows)
    wr = wp / len(with_rows) if with_rows else 0.0
    wor = wop / len(without_rows) if without_rows else 0.0
    summary = ROOT / "experiments/analysis/PACKET_REPLAY_CONFIRM_SUMMARY.md"
    summary.write_text(
        f"Requests: {sources} packet-exposed source requests; {len(rows)} completed reissues.\n\n"
        f"With packet: {wp}/{len(with_rows)} warm passes ({wr:.3f}).\n\n"
        f"Without packet: {wop}/{len(without_rows)} warm passes ({wor:.3f}).\n\n"
        f"Paired difference (with minus without): {wr - wor:+.3f}.\n"
    )
    if result.get("status") == "complete":
        append_log(f"confirm replay pushed: {sources} requests.")
    else:
        append_log(
            f"confirm replay skipped remaining requests at the fixed $3 cap: "
            f"{len(rows)}/{result.get('planned_jobs', '?')} reissues terminal."
        )
    message = (
        "Archive roots experiments/analysis/packet-replay-confirm.csv and "
        "experiments/analysis/PACKET_REPLAY_CONFIRM_SUMMARY.md; "
        f"{len(rows)} replay cells; passes per variant: with-packet {wp}/{len(with_rows)}, "
        f"without-packet {wop}/{len(without_rows)}"
    )
    append_log("PUSH: " + message)
    git("add", "experiments/analysis/packet-replay-confirm.csv",
        "experiments/analysis/PACKET_REPLAY_CONFIRM_SUMMARY.md",
        "experiments/stage6-expanded/LOG.md")
    git("commit", "-m", message)
    git("push", "origin", "HEAD:evidence/results-20260902")
    return True


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
        terminal, running, queued = state_counts(state)
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
        solo_state = read_state(SOLO_REMOTE)
        solo_terminal, solo_running, solo_queued = state_counts(solo_state)
        if solo_state and solo_queued == 0 and "qq arm launched" not in log_text:
            branch = git("ls-remote", "origin", "refs/heads/qq-arm-v1", check=False)
            if branch.returncode == 0 and branch.stdout.strip():
                launch = subprocess.run(
                    ("sh", str(ROOT / "scripts/launch_stage6_qq_arm.sh")),
                    cwd=ROOT, text=True, capture_output=True,
                )
                if launch.returncode != 0:
                    append_log(f"qq arm prelaunch gate not ready: {launch.stderr.strip()}")
                    changed = True
                log_text = LOG.read_text() if LOG.exists() else log_text
        for when in (clock_time(21, 30), clock_time(22, 30), clock_time(23, 30), clock_time(0, 30)):
            marker = when.strftime("%H:%M PT confirm status")
            due = now_pt().time() >= when if when.hour else now_pt().time() < clock_time(12, 0) and now_pt().time() >= when
            if due and marker not in log_text:
                arm_text = ", ".join(f"{arm} {passed[arm]}/{totals[arm]}" for arm in ARMS)
                waves = f"confirm {terminal}/{running}/{queued} terminal/running/queued"
                if solo_state:
                    waves += f"; solo {solo_terminal}/{solo_running}/{solo_queued}"
                qq_state = read_state(QQ_REMOTE)
                if qq_state:
                    qt, qr, qq = state_counts(qq_state)
                    waves += f"; qq {qt}/{qr}/{qq}"
                append_log(f"{marker} — {waves}; passes {arm_text}.")
                log_text += marker
                changed = True
        if now_pt().time() >= clock_time(23, 0) and "solo extension launched" not in log_text and "solo extension skipped:" not in log_text:
            append_log("solo extension skipped: not all 128 primary cells had dispatched by the 23:00 PT cutoff.")
            log_text += "solo extension skipped:"
            changed = True
        if state.get("phase") == "complete" and "confirm complete," not in log_text:
            append_log(f"confirm complete, {terminal} cells terminal; replay gate ready.")
            changed = True
        c1_tasks = [
            item for task_id, item in state.get("tasks", {}).items()
            if task_id.endswith("-c1plus-fill-reserve")
        ]
        c1_terminal = c1_tasks and all(
            item.get("status") in {"complete", "exited_incomplete"} for item in c1_tasks
        )
        if c1_terminal and "confirm replay launched" not in log_text:
            launch = subprocess.run(
                ("sh", str(ROOT / "scripts/launch_stage6_confirm_replay.sh")),
                cwd=ROOT, text=True, capture_output=True,
            )
            if launch.returncode != 0:
                append_log(f"confirm replay prelaunch failed: {launch.stderr.strip()}")
                changed = True
            log_text = LOG.read_text() if LOG.exists() else log_text
        if maybe_finish_replay(log_text):
            log_text = LOG.read_text()
        if changed or time.monotonic() - last_push >= 1800:
            push(results)
            last_push = time.monotonic()
        time.sleep(60)


if __name__ == "__main__":
    raise SystemExit(main())
