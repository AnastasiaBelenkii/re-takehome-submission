#!/usr/bin/env python3
"""No-key Docker preflight of the call-zero tactic on every pristine challenge."""

from __future__ import annotations

import asyncio
import json
import sys
import tempfile
import uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "src"), str(ROOT)]

from collaboration_engine_v2.experiment import LEAN_IMAGE
from collaboration_engine_v2.tactics import declarations_unchanged, tactic_candidate
from re_harness.events import EventLogger
from re_harness.lean import LeanClient


async def run() -> list[dict[str, object]]:
    manifest = json.loads((ROOT / "sample-problems/manifest.json").read_text())
    with tempfile.TemporaryDirectory(prefix="collab-v2-preflight-") as temporary:
        lean = LeanClient(image=LEAN_IMAGE,
                          events=EventLogger(Path(temporary) / "events.jsonl", problem_id="preflight"),
                          session_id=uuid.uuid4().hex, timeout_s=120)
        records = []
        try:
            for item in manifest["problems"]:
                challenge = (ROOT / "sample-problems" / item["id"] / "challenge.lean").read_text()
                candidate = tactic_candidate(challenge)
                if candidate is None or not declarations_unchanged(challenge, candidate):
                    raise RuntimeError(f"declaration-preserving substitution failed for {item['id']}")
                check = await lean.check_file(candidate)
                records.append({"problem": item["id"], "accepted": check.accepted,
                                "timed_out": check.timed_out,
                                "diagnostic_count": len(check.messages)})
        finally:
            lean.close()
    return records


if __name__ == "__main__":
    rows = asyncio.run(run())
    print(json.dumps({"problems": rows, "accepted": sum(bool(row["accepted"]) for row in rows),
                      "declarations_unchanged": len(rows)}, indent=2))
