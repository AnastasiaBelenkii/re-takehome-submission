#!/usr/bin/env python3
"""Freeze every packet-exposed request in the Stage 6 confirm C1+ cells."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

MARKER = "Compiler-validated peer skeleton: fill its residual holes now."
REQUEST_KEYS = (
    "model", "messages", "max_tokens", "temperature", "top_p", "seed",
    "stop", "reasoning", "tools", "tool_choice",
)


def digest(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def challenge_from_messages(messages: list[dict[str, Any]]) -> str:
    joined = "\n".join(str(message.get("content", "")) for message in messages)
    matches = re.findall(
        r"Pristine Lean challenge:\s*```(?:lean|lean4)?\s*\n(.*?)```",
        joined, flags=re.DOTALL | re.IGNORECASE,
    )
    if not matches:
        raise ValueError("request has no pristine Lean challenge block")
    return matches[-1].strip() + "\n"


def task_from_path(path: Path) -> str:
    for part in path.parts:
        if part.startswith("stage6-confirm-"):
            return part
    return path.parent.name


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    records: dict[str, dict[str, Any]] = {}
    for path in sorted(args.archive.rglob("transcript.json")):
        if "c1plus-fill-reserve" not in str(path):
            continue
        try:
            transcript = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        problem = str(transcript.get("problem_id", ""))
        for call in transcript.get("calls", []):
            request = call.get("request") or {}
            messages = request.get("messages") or []
            if MARKER not in "\n".join(str(item.get("content", "")) for item in messages):
                continue
            call_id = str(call.get("call_id", ""))
            if not call_id:
                raise ValueError(f"packet-exposed call without call_id in {path}")
            challenge = challenge_from_messages(messages)
            replay_request = {
                key: copy.deepcopy(request[key]) for key in REQUEST_KEYS if key in request
            }
            model = str(request["model"])
            source_model = (
                "qwen/qwen3.5-flash-02-23"
                if model == "openai/gpt-oss-120b" else "openai/gpt-oss-120b"
            )
            record = {
                "source_wave": "wave_d",
                "source_task": task_from_path(path),
                "source_transcript": str(path.relative_to(args.archive)),
                "source_call_id": call_id,
                "problem": problem,
                "direction": f"{source_model} -> {model}",
                "base_imports": "import Mathlib",
                "challenge": challenge,
                "request": replay_request,
                "request_sha256": digest(json.dumps(replay_request, sort_keys=True)),
            }
            if call_id in records and records[call_id] != record:
                raise ValueError(f"conflicting duplicate call_id {call_id}")
            records[call_id] = record
    manifest = {
        "schema_version": 1,
        "experiment": "packet-replay-stage6-confirm-v1",
        "created_at": datetime.now(UTC).isoformat(),
        "selection": "all marker-bearing requests in primary-confirm c1plus-fill-reserve cells",
        "samples": list(range(1, 9)),
        "variants": ["with_packet", "without_packet"],
        "budget_cap_usd": 3.0,
        "records": sorted(records.values(), key=lambda item: item["source_call_id"]),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.output.with_suffix(".tmp")
    temporary.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    temporary.replace(args.output)
    print(json.dumps({"source_requests": len(records), "paid_jobs": len(records) * 16}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
