#!/usr/bin/env python3
"""Replay conservative partial-proof salvage over stored evaluator artifacts.

The script makes no model calls.  It reconstructs checked candidates from the
transcript, joins them to their recorded Lean diagnostics by source hash, and
optionally validates proposed skeletons with the same warm Lean image.
"""

from __future__ import annotations

import argparse
import asyncio
import hashlib
import json
import sys
import tempfile
import uuid
from collections import Counter
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "src"), str(ROOT)]

from baselines.simple_agent import _extract_lean
from collaboration_engine_v2.experiment import LEAN_IMAGE
from collaboration_engine_v2.salvage import compiles_with_sorry, propose_sorrifications
from collaboration_engine_v2.tactics import canonicalize_imports
from re_harness.events import EventLogger
from re_harness.lean import LeanClient


def _sha256(source: str) -> str:
    return hashlib.sha256(source.encode("utf-8")).hexdigest()


def _response_content(call: dict[str, Any]) -> str | None:
    if call.get("status") != "ok":
        return None
    try:
        value = call["response"]["choices"][0]["message"]["content"]
    except (KeyError, IndexError, TypeError):
        return None
    return value if isinstance(value, str) else None


def _identity(path: Path) -> tuple[str, str, str]:
    parts = path.parts
    task = next((part for part in parts if part.startswith("stage3v1-")), path.parent.name)
    condition = task.rsplit("-", 1)[-1] if "-" in task else "unknown"
    problem = path.parent.name
    return task, condition, problem


def collect(root: Path, *, limit: int | None) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    records: list[dict[str, Any]] = []
    stats: Counter[str] = Counter()
    seen: set[tuple[str, str]] = set()
    for transcript_path in sorted(root.rglob("transcript.json")):
        events_path = transcript_path.with_name("events.jsonl")
        if not events_path.exists():
            continue
        stats["transcripts"] += 1
        transcript = json.loads(transcript_path.read_text())
        checks: dict[str, list[dict[str, Any]]] = {}
        for line in events_path.read_text().splitlines():
            event = json.loads(line)
            if event.get("event") == "lean_check":
                checks.setdefault(str(event.get("source_sha256")), []).append(event["result"])
        task, condition, problem = _identity(transcript_path)
        for call_index, call in enumerate(transcript.get("calls", []), start=1):
            stats["calls"] += 1
            content = _response_content(call)
            if content is None:
                stats["non_ok_or_unreadable_calls"] += 1
                continue
            source = canonicalize_imports(_extract_lean(content, fallback=""))
            source_hash = _sha256(source)
            matches = checks.get(source_hash, [])
            if not matches:
                stats["unmatched_calls"] += 1
                continue
            result = matches.pop(0)
            stats["matched_checks"] += 1
            if result.get("accepted"):
                stats["accepted"] += 1
                continue
            if result.get("timed_out"):
                stats["timed_out"] += 1
                continue
            proposals = propose_sorrifications(source, result.get("messages", []))
            if not proposals:
                stats["ineligible_failures"] += 1
                continue
            stats["eligible_failures"] += 1
            key = (source_hash, json.dumps(result.get("messages", []), sort_keys=True))
            if key in seen:
                stats["duplicate_eligible_failures"] += 1
                continue
            seen.add(key)
            first = proposals[0]
            model = str(call.get("request", {}).get("model", "unknown"))
            records.append({
                "task": task,
                "condition": condition,
                "problem": problem,
                "model": model,
                "call": call_index,
                "parent_sha256": source_hash,
                "parent_lines": len(source.splitlines()),
                "proposal_count": len(proposals),
                "first_mode": first.mode,
                "first_retained_lines": first.retained_lines,
                "first_retained_source_fraction": round(
                    first.retained_lines / max(1, len(source.splitlines())), 4
                ),
                "residual_chars": len(first.residual_goals),
                "_proposals": proposals,
            })
    if limit is not None and len(records) > limit:
        # Hash ordering is deterministic and avoids selecting one contiguous
        # task/problem prefix from the artifact tree.
        records = sorted(records, key=lambda item: item["parent_sha256"])[:limit]
    return records, dict(stats)


async def validate(records: list[dict[str, Any]], *, timeout_s: int) -> dict[str, Any]:
    counts: Counter[str] = Counter()
    by_problem: dict[str, Counter[str]] = {}
    by_model: dict[str, Counter[str]] = {}
    with tempfile.TemporaryDirectory(prefix="salvage-replay-") as temporary:
        lean = LeanClient(
            image=LEAN_IMAGE,
            events=EventLogger(Path(temporary) / "events.jsonl", problem_id="salvage-replay"),
            session_id=uuid.uuid4().hex,
            timeout_s=120,
        )
        try:
            for record in records:
                counts["candidates"] += 1
                compiled = False
                selected_mode = None
                checks_used = 0
                for proposal in record.pop("_proposals"):
                    if proposal.retained_lines <= 0:
                        continue
                    check = await lean.check_file(proposal.source, timeout_s=timeout_s)
                    checks_used += 1
                    counts["warm_checks"] += 1
                    counts["warm_check_duration_ms"] += int(check.duration_ms)
                    counts["warm_check_timeouts"] += int(check.timed_out)
                    if compiles_with_sorry(proposal.source, check):
                        compiled = True
                        selected_mode = proposal.mode
                        record["selected_retained_lines"] = proposal.retained_lines
                        break
                record["compiled_skeleton"] = compiled
                record["selected_mode"] = selected_mode
                record["warm_checks"] = checks_used
                bucket_problem = by_problem.setdefault(record["problem"], Counter())
                bucket_model = by_model.setdefault(record["model"], Counter())
                bucket_problem["eligible"] += 1
                bucket_model["eligible"] += 1
                if compiled:
                    counts["compiled_skeletons"] += 1
                    bucket_problem["compiled"] += 1
                    bucket_model["compiled"] += 1
        finally:
            lean.close()
    return {
        **counts,
        "compiled_yield": round(counts["compiled_skeletons"] / max(1, counts["candidates"]), 4),
        "by_problem": {key: dict(value) for key, value in sorted(by_problem.items())},
        "by_model": {key: dict(value) for key, value in sorted(by_model.items())},
    }


async def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("artifact_root", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--max-candidates", type=int)
    parser.add_argument("--check-timeout-s", type=int, default=2)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    records, collection = collect(args.artifact_root, limit=args.max_candidates)
    validation = (
        await validate(records, timeout_s=args.check_timeout_s)
        if args.validate else {"candidates": len(records)}
    )
    for record in records:
        record.pop("_proposals", None)
    payload = {
        "schema_version": 1,
        "artifact_root": str(args.artifact_root.resolve()),
        "model_calls_made": 0,
        "salvage_check_timeout_s": args.check_timeout_s,
        "collection": collection,
        "validation": validation,
        "records": records,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"collection": collection, "validation": validation}, indent=2))


if __name__ == "__main__":
    asyncio.run(main())
