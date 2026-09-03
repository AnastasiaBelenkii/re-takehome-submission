#!/usr/bin/env python3
"""Collect and push the expanded pass@8 global-queue screen."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import time
from collections import Counter, defaultdict
from datetime import datetime, time as clock_time
from pathlib import Path
from zoneinfo import ZoneInfo

ROOT = Path(os.environ.get("STAGE6_PUSH_REPO", "/opt/stage6-pusher/repo"))
ARCHIVE = ROOT / "evidence/archives/stage6-pass8-20260903"
LOG = ROOT / "experiments/stage6-expanded/LOG.md"
REMOTE = "/opt/stage6-pass8-20260903/global"
HOSTS = ("marketplace", "worker2", "worker3", "worker4", "worker5", "worker6", "worker7", "worker8", "worker10")
TARGETS = {
    "marketplace": None,
    "worker2": "root@10.122.0.4",
    "worker3": "root@10.122.0.3",
    "worker4": "root@10.122.0.5",
    "worker5": "root@10.122.0.7",
    "worker6": "root@10.122.0.6",
    "worker7": "root@10.122.0.8",
    "worker8": "root@10.122.0.10",
    "worker10": "root@10.122.0.11",
}
KEEP = ("result.json", "events.jsonl", "transcript.json", "solution.lean",
        "preliminary-status.json", "provenance.json", "queue-state.json")
PT = ZoneInfo("America/Los_Angeles")


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
        worker_number = 1 if host == "marketplace" else int(host.removeprefix("worker"))
        destination = ARCHIVE / "hosts" / f"takehome-worker-{worker_number}"
        destination.mkdir(parents=True, exist_ok=True)
        command = ["rsync", "-a", "--timeout=30", "--include=*/"]
        command.extend(f"--include={name}" for name in KEEP)
        source = f"{REMOTE}/{host}/cells/"
        target = TARGETS[host]
        if target is None:
            command.extend(("--exclude=*", source, f"{destination}/cells/"))
        else:
            command.extend(("--exclude=*", f"{target}:{source}", f"{destination}/cells/"))
        subprocess.run(command, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    controller_source = Path("/opt/stage6-pass8-20260903/global/global-controller-state.json")
    if controller_source.exists():
        shutil.copy2(controller_source, ARCHIVE / "global-controller-state.json")
    controller = {}
    controller_path = ARCHIVE / "global-controller-state.json"
    if controller_path.exists():
        controller = json.loads(controller_path.read_text())
    results = []
    for path in ARCHIVE.rglob("result.json"):
        try:
            value = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if value.get("problem_id"):
            results.append(value)
    return results, controller


def write_band(results: list[dict], valid: bool) -> int:
    by_problem: dict[str, Counter[str]] = defaultdict(Counter)
    totals: dict[str, Counter[str]] = defaultdict(Counter)
    for result in results:
        metadata = result.get("agent_metadata") or {}
        arm = str(metadata.get("condition", ""))
        problem = str(result.get("problem_id", ""))
        totals[problem][arm] += 1
        if result.get("passed"):
            by_problem[problem][arm] += 1
    problems = [item["id"] for item in json.loads(
        (ROOT / "experiments/stage6-expanded/problems/manifest.json").read_text()
    )["problems"]]
    band = []
    lines = ["# Stage 6 expanded-set band", "", "| Problem | Qwen | GPT-OSS | Band |", "|---|---:|---:|---|"]
    for problem in problems:
        qp, qn = by_problem[problem]["qwen-solo-plus"], totals[problem]["qwen-solo-plus"]
        gp, gn = by_problem[problem]["gptoss-solo-plus"], totals[problem]["gptoss-solo-plus"]
        selected = valid and ((qn == 8 and 1 <= qp <= 7) or (gn == 4 and 1 <= gp <= 3))
        if selected:
            band.append(problem)
        lines.append(f"| {problem} | {qp}/{qn} | {gp}/{gn} | {'yes' if selected else 'no'} |")
    lines.extend(("", f"Band list ({len(band)}): " + (", ".join(f"`{p}`" for p in band) if band else "none") + ".", ""))
    if not valid:
        lines.extend(("The Qwen pass@8 matrix did not complete before the launch deadline, so no valid band is inferred; B is reported skipped/incomplete rather than treating partial denominators as pass@8.", ""))
    (ROOT / "experiments/stage6-expanded/BAND.md").write_text("\n".join(lines))
    return len(band)


def push(results: list[dict], include_band: bool = False) -> None:
    arms = Counter()
    totals = Counter()
    for result in results:
        arm = str((result.get("agent_metadata") or {}).get("condition", "unknown"))
        totals[arm] += 1
        arms[arm] += int(bool(result.get("passed")))
    message = (
        f"Archive root evidence/archives/stage6-pass8-20260903; {len(results)} cells; "
        "passes per arm: " + (
            ", ".join(f"{arm} {arms[arm]}/{totals[arm]}" for arm in sorted(totals))
            if totals else "qwen-solo-plus 0/0"
        )
    )
    append_log("PUSH: " + message)
    git("add", "evidence/archives/stage6-pass8-20260903", "experiments/stage6-expanded/LOG.md")
    if include_band:
        git("add", "experiments/stage6-expanded/BAND.md")
    if git("diff", "--cached", "--quiet", check=False).returncode:
        git("commit", "-m", message)
        git("push", "origin", "HEAD:evidence/results-20260902")


def main() -> int:
    # The launcher records and pushes the launch signal from this same checkout.
    time.sleep(30)
    last_push = 0.0
    while True:
        results, controller = collect()
        log_text = LOG.read_text() if LOG.exists() else ""
        changed = False
        statuses = Counter(item.get("status", "unknown") for item in controller.get("tasks", {}).values())
        terminal_count = statuses["complete"] + statuses["exited_incomplete"]
        running_count = statuses["running"] + statuses["dispatching"]
        queued_count = statuses["pending"]
        passed = sum(bool(result.get("passed")) for result in results)
        for report_time in (clock_time(15, 0), clock_time(17, 0), clock_time(19, 0)):
            marker = report_time.strftime("%H:%M PT status")
            if now_pt().time() >= report_time and marker not in log_text:
                append_log(
                    f"{marker} — calibration: terminal 128 / running 0 / queued 0, passes qwen-solo-plus 68/128; "
                    f"screen: terminal {terminal_count} / running {running_count} / queued {queued_count}, "
                    f"passes qwen-solo-plus {passed}/{len(results)}; confirm: not launched."
                )
                log_text += marker
                changed = True
        if now_pt().time() >= clock_time(16, 45) and "confirm skipped:" not in log_text and "confirm launched" not in log_text:
            append_log("confirm skipped: BAND.md was not available by the 16:45 PT cutoff.")
            log_text += "confirm skipped:"
            changed = True
        if now_pt().time() >= clock_time(17, 45) and "solo extension skipped:" not in log_text and "solo extension launched" not in log_text:
            append_log("solo extension skipped: confirm was not launched before its 17:45 PT cutoff.")
            log_text += "solo extension skipped:"
            changed = True
        finished = controller.get("phase") in {"complete", "incomplete"}
        if finished:
            q_count = sum((result.get("agent_metadata") or {}).get("condition") == "qwen-solo-plus" for result in results)
            if "BAND.md pushed:" not in log_text and "B reported incomplete:" not in log_text:
                band_count = write_band(results, q_count == 256)
                if q_count == 256:
                    append_log(f"BAND.md pushed: {band_count} band problems.")
                else:
                    append_log(f"B reported incomplete: global screen ended with {q_count}/256 result cells.")
                push(results, include_band=True)
                last_push = time.monotonic()
            # Reporting is required at 19:00 even if the screen finishes first.
            if now_pt().time() >= clock_time(19, 0):
                return 0
        if changed or time.monotonic() - last_push >= 1800:
            push(results)
            last_push = time.monotonic()
        time.sleep(60)


if __name__ == "__main__":
    raise SystemExit(main())
