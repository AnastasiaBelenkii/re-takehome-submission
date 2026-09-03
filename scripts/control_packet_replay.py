#!/usr/bin/env python3
"""Collect a completed worker-9 replay and release the queued rmo tail."""

from __future__ import annotations

import json
import subprocess
import time
from datetime import UTC, datetime
from pathlib import Path


WORKER = "takehome-worker-9"
REMOTE_ROOT = "/opt/packet-replay-wave-a-c-v1-20260903"
ROOT = Path(__file__).resolve().parents[1]
LOCAL_ROOT = ROOT / "experiments/analysis/packet-replay-runtime"
FINAL_CSV = ROOT / "experiments/analysis/packet-replay.csv"
FINAL_RESULT = ROOT / "experiments/analysis/packet-replay-result.json"
COMPLETE_MARKER = Path("/tmp/stage5-packet-replay-complete.json")


def main() -> int:
    while True:
        check = subprocess.run(
            ["ssh", WORKER, f"test -f {REMOTE_ROOT}/result.json && cat {REMOTE_ROOT}/result.json"],
            capture_output=True,
            text=True,
        )
        if check.returncode == 0 and check.stdout.strip():
            result = json.loads(check.stdout)
            if result.get("status") == "failed":
                active = subprocess.run(
                    ["ssh", WORKER, "tmux has-session -t packet_replay_wave_a_c_v1"],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                )
                if active.returncode != 0:
                    return 1
            if result.get("status") in {"complete", "budget_cap"}:
                LOCAL_ROOT.mkdir(parents=True, exist_ok=True)
                subprocess.run(
                    ["rsync", "-a", f"{WORKER}:{REMOTE_ROOT}/", f"{LOCAL_ROOT}/"],
                    check=True,
                )
                source = LOCAL_ROOT / "packet-replay.csv"
                temporary = FINAL_CSV.with_suffix(".csv.tmp")
                temporary.write_bytes(source.read_bytes())
                temporary.replace(FINAL_CSV)
                result_temporary = FINAL_RESULT.with_suffix(".json.tmp")
                result_temporary.write_bytes((LOCAL_ROOT / "result.json").read_bytes())
                result_temporary.replace(FINAL_RESULT)
                subprocess.run(
                    ["git", "add", str(FINAL_CSV.relative_to(ROOT)),
                     str(FINAL_RESULT.relative_to(ROOT))],
                    cwd=ROOT,
                    check=True,
                )
                subprocess.run(
                    ["git", "commit", "-m",
                     f"Record completed packet replay ({result['completed_rows']} rows)"],
                    cwd=ROOT,
                    check=True,
                )
                subprocess.run(
                    ["git", "push", "origin", "salvage-fill-reserve-v2"],
                    cwd=ROOT,
                    check=True,
                )
                marker = {
                    "completed_at": datetime.now(UTC).isoformat(),
                    "remote_root": REMOTE_ROOT,
                    "result": result,
                }
                COMPLETE_MARKER.write_text(json.dumps(marker, indent=2, sort_keys=True) + "\n")
                return 0
        time.sleep(15)


if __name__ == "__main__":
    raise SystemExit(main())
