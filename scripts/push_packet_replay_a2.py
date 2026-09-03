#!/usr/bin/env python3
"""Durably collect, summarize, and push the fixed A2 replay shards."""

from __future__ import annotations

import csv
import json
import os
import shutil
import subprocess
import time
from collections import Counter
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

ROOT = Path(os.environ.get("STAGE6_PUSH_REPO", "/opt/stage6-pusher/repo"))
RUNTIME = Path(os.environ.get("STAGE6_PUSH_RUNTIME", "/opt/stage6-pusher/runtime"))
LOG = ROOT / "experiments/stage6-expanded/LOG.md"
ANALYSIS = ROOT / "experiments/analysis"
JOBS = (
    ("marketplace", "k8-batch1"),
    ("worker2", "k8-batch2"),
    ("worker3", "k8-batch3"),
    ("worker4", "k8-batch4"),
    ("worker5", "wave-a-shard1"),
    ("worker6", "wave-a-shard2"),
    ("worker7", "wave-a-shard3"),
    ("worker8", "wave-a-shard4"),
)
REMOTE_ROOT = "/opt/packet-replay-a2-20260903"
FIELDS = (
    "source_wave", "source_task", "source_call_id", "problem", "direction",
    "model", "variant", "sample", "seed", "temperature", "reasoning",
    "response_id", "finish_reason", "warm_accepted", "warm_timed_out",
    "warm_duration_ms", "warm_message_count", "prompt_tokens",
    "completion_tokens", "total_tokens", "cost_usd", "latency_ms",
    "candidate_sha256", "error",
)


def run(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(args, cwd=ROOT, text=True, capture_output=True, check=check)


def now_pt() -> str:
    return datetime.now(ZoneInfo("America/Los_Angeles")).strftime("%H:%M PT")


def collect() -> tuple[list[dict[str, str]], list[dict[str, str]], bool]:
    k8: list[dict[str, str]] = []
    wave_a: list[dict[str, str]] = []
    complete = True
    RUNTIME.mkdir(parents=True, exist_ok=True)
    for host, job in JOBS:
        local = RUNTIME / job
        local.mkdir(parents=True, exist_ok=True)
        subprocess.run(
            ["rsync", "-a", "--timeout=30", f"{host}:{REMOTE_ROOT}/{job}/", f"{local}/"],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
        )
        result_path = local / "result.json"
        if not result_path.exists() or json.loads(result_path.read_text()).get("status") != "complete":
            complete = False
        csv_path = local / "packet-replay.csv"
        if not csv_path.exists():
            continue
        with csv_path.open(newline="") as handle:
            rows = list(csv.DictReader(handle))
        (k8 if job.startswith("k8-") else wave_a).extend(rows)
    return k8, wave_a, complete


def write_csv(path: Path, rows: list[dict[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerows(sorted(rows, key=lambda row: (
            row["source_wave"], row["source_call_id"], row["variant"],
            int(row["sample"]),
        )))
    temporary.replace(path)


def pass_counts(rows: list[dict[str, str]]) -> Counter[str]:
    return Counter(
        row["variant"] for row in rows
        if row.get("warm_accepted", "").lower() == "true" and not row.get("error")
    )


def summarize(k8: list[dict[str, str]], wave_a: list[dict[str, str]], complete: bool) -> str:
    kc = pass_counts(k8)
    ac = pass_counts(wave_a)
    c_rows = [row for row in k8 if row["source_wave"] == "wave_c"]
    d_rows = [row for row in k8 if row["source_wave"] == "wave_d"]
    state = "completed" if complete else "in progress"
    return (
        f"The A2 replay is {state}. It contains {len(c_rows)} Wave C and {len(d_rows)} "
        f"Wave D requests in the K=8 file, with warm-pass counts "
        f"{kc['with_packet']} with packet and {kc['without_packet']} without packet; "
        f"the separate Wave A completion contains {len(wave_a)} requests, with warm-pass "
        f"counts {ac['with_packet']} with packet and {ac['without_packet']} without packet. "
        "Counts are paid replay requests (source prompts × variant × fresh sample), and the "
        "original K=2 rows remain only in packet-replay.csv.\n"
    )


def append_log(line: str) -> None:
    with LOG.open("a") as handle:
        handle.write(f"- {now_pt()} — {line}\n")


def push(k8: list[dict[str, str]], wave_a: list[dict[str, str]], complete: bool) -> None:
    write_csv(ANALYSIS / "packet-replay-k8.csv", k8)
    write_csv(ANALYSIS / "packet-replay-wave-a-full.csv", wave_a)
    (ANALYSIS / "PACKET_REPLAY_A2_SUMMARY.md").write_text(summarize(k8, wave_a, complete))
    kc, ac = pass_counts(k8), pass_counts(wave_a)
    message = (
        "Archive roots: experiments/analysis/packet-replay-k8.csv and "
        "experiments/analysis/packet-replay-wave-a-full.csv; "
        f"{len(k8) + len(wave_a)} requests; passes per variant: "
        f"k8 with {kc['with_packet']}, without {kc['without_packet']}; "
        f"wave-a-full with {ac['with_packet']}, without {ac['without_packet']}"
    )
    append_log("PUSH: " + message)
    run("git", "add", "experiments/analysis/packet-replay-k8.csv",
        "experiments/analysis/packet-replay-wave-a-full.csv",
        "experiments/analysis/PACKET_REPLAY_A2_SUMMARY.md",
        "experiments/stage6-expanded/LOG.md")
    staged = run("git", "diff", "--cached", "--quiet", check=False).returncode != 0
    if staged:
        run("git", "commit", "-m", message)
        run("git", "push", "origin", "HEAD:evidence/results-20260902")


def main() -> int:
    while True:
        k8, wave_a, complete = collect()
        push(k8, wave_a, complete)
        if complete:
            c_sources = len({row["source_call_id"] for row in k8 if row["source_wave"] == "wave_c"})
            d_sources = len({row["source_call_id"] for row in k8 if row["source_wave"] == "wave_d"})
            a_sources = len({row["source_call_id"] for row in wave_a})
            append_log(f"replay-k8 pushed: {c_sources} Wave C + {d_sources} Wave D requests; wave-a-full pushed: {a_sources} requests.")
            push(k8, wave_a, complete)
            return 0
        time.sleep(1800)


if __name__ == "__main__":
    raise SystemExit(main())
