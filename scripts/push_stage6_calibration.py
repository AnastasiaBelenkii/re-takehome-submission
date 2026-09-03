#!/usr/bin/env python3
"""Collect, summarize, and push the 128-cell Stage 6 calibration every 30 minutes."""

from __future__ import annotations

import json
import os
import subprocess
import time
from collections import Counter, defaultdict
from datetime import datetime
from pathlib import Path
from statistics import median
from zoneinfo import ZoneInfo

ROOT = Path(os.environ.get("STAGE6_PUSH_REPO", "/opt/stage6-pusher/repo"))
ARCHIVE = ROOT / "evidence/archives/stage6-calibration-20260903"
LOG = ROOT / "experiments/stage6-expanded/LOG.md"
REMOTE = "/opt/stage6-calibration-20260903"
HOSTS = ("marketplace", "worker2", "worker3", "worker4", "worker5", "worker6", "worker7", "worker8")
KEEP = ("result.json", "events.jsonl", "transcript.json", "solution.lean",
        "preliminary-status.json", "provenance.json", "queue-state.json")


def now_pt() -> str:
    return datetime.now(ZoneInfo("America/Los_Angeles")).strftime("%H:%M PT")


def git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(("git", *args), cwd=ROOT, text=True, capture_output=True, check=check)


def collect() -> tuple[list[tuple[Path, dict]], bool]:
    ARCHIVE.mkdir(parents=True, exist_ok=True)
    for index, host in enumerate(HOSTS, 1):
        destination = ARCHIVE / "hosts" / f"takehome-worker-{index}"
        destination.mkdir(parents=True, exist_ok=True)
        command = ["rsync", "-a", "--timeout=30", "--include=*/"]
        command.extend(f"--include={name}" for name in KEEP)
        command.extend(("--exclude=*", f"{host}:{REMOTE}/worker{index}/", f"{destination}/"))
        subprocess.run(command, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    results: list[tuple[Path, dict]] = []
    for path in ARCHIVE.rglob("result.json"):
        try:
            result = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if result.get("problem_id"):
            results.append((path, result))
    states = list(ARCHIVE.rglob("queue-state.json"))
    terminal = len(states) == 8 and all(
        json.loads(path.read_text()).get("phase") != "running" for path in states
    )
    return results, terminal


def append_log(line: str) -> None:
    with LOG.open("a") as handle:
        handle.write(f"- {now_pt()} — {line}\n")


def write_calibration(results: list[tuple[Path, dict]]) -> None:
    counts: dict[str, list[bool]] = defaultdict(list)
    for _, result in results:
        counts[str(result["problem_id"])].append(bool(result.get("passed")))
    ceiling = {"p01_linear", "p02_frac_cancel", "p04_sum_sq", "p05_gcd_mersenne", "p06_pow_mod", "p10_factorial_pow"}
    floor = {"putnam_2018_a1", "putnam_2020_a2", "rmo_2000_2", "rmo_2000_3", "rmo_2000_6", "rmo_2001_2"}
    band = {"p03_sq_ge_two_ab", "p07_least_divisible", "p08_sum_products", "p09_imo1964"}
    lines = ["# Stage 6 calibration", "", "Qwen solo-plus, seeds 7001–7008, at most 10 calls per cell.", "", "| Problem | pass@8 | Known class |", "|---|---:|---|"]
    order = ["p01_linear", "p02_frac_cancel", "p03_sq_ge_two_ab", "p04_sum_sq", "p05_gcd_mersenne", "p06_pow_mod", "p07_least_divisible", "p08_sum_products", "p09_imo1964", "p10_factorial_pow", "putnam_2018_a1", "putnam_2020_a2", "rmo_2000_2", "rmo_2000_3", "rmo_2000_6", "rmo_2001_2"]
    for problem in order:
        label = "ceiling" if problem in ceiling else "floor" if problem in floor else "band" if problem in band else "unclassified"
        values = counts.get(problem, [])
        lines.append(f"| {problem} | {sum(values)}/{len(values)} | {label} |")
    observed_band = sorted(problem for problem, values in counts.items() if 0 < sum(values) < len(values))
    lines.extend(("", "The known ceiling, floor, and band labels above were fixed in the assignment extension before this calibration. The mechanically observed 1–7/8 band is: " + (", ".join(observed_band) if observed_band else "none") + ".", ""))
    outcome_rows = []
    for label, passed in (("solved", True), ("failed", False)):
        selected = [result for _, result in results if bool(result.get("passed")) is passed]
        calls = [int((result.get("agent_metadata") or {}).get("calls_dispatched", 0)) for result in selected]
        walls = [float(result.get("wall_s", 0.0)) for result in selected]
        outcome_rows.append((label, len(selected), median(calls), median(walls)))
    lines.extend((
        "## Effort by outcome", "",
        "| Outcome | Cells | Median model calls | Median wall time (s) |",
        "|---|---:|---:|---:|",
    ))
    lines.extend(f"| {label} | {count} | {calls:g} | {wall:.1f} |" for label, count, calls, wall in outcome_rows)
    lines.append("")
    (ROOT / "experiments/stage6-expanded/CALIBRATION.md").write_text("\n".join(lines))


def push(results: list[tuple[Path, dict]], complete: bool) -> None:
    passes = sum(bool(result.get("passed")) for _, result in results)
    message = f"Archive root evidence/archives/stage6-calibration-20260903; {len(results)} cells; passes per arm: qwen-solo-plus {passes}/{len(results)}"
    append_log("PUSH: " + message)
    git("add", "evidence/archives/stage6-calibration-20260903", "experiments/stage6-expanded/LOG.md")
    if complete:
        write_calibration(results)
        git("add", "experiments/stage6-expanded/CALIBRATION.md")
    if git("diff", "--cached", "--quiet", check=False).returncode:
        git("commit", "-m", message)
        git("push", "origin", "HEAD:evidence/results-20260902")


def main() -> int:
    while True:
        results, complete = collect()
        if complete and len(results) == 128:
            append_log("calibration complete, 128 cells, CALIBRATION.md pushed.")
        push(results, complete)
        if complete:
            return 0
        time.sleep(1800)


if __name__ == "__main__":
    raise SystemExit(main())
