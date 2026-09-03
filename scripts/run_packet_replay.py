#!/usr/bin/env python3
"""Prepare and run the frozen Wave A/C counterfactual packet replay."""

from __future__ import annotations

import argparse
import asyncio
import copy
import csv
import hashlib
import json
import os
import re
import sys
import time
import uuid
from collections import defaultdict
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "src"), str(ROOT)]

from baselines.simple_agent import _extract_lean
from collaboration_engine_v2.experiment import LEAN_IMAGE
from collaboration_engine_v2.tactics import canonicalize_imports
from re_harness.budget import BudgetExceeded, BudgetLedger
from re_harness.events import EventLogger
from re_harness.lean import LeanClient, pristine_import_block
from re_harness.llm import LLMClient


MARKERS = {
    "wave_a": "Evidence from an independent solver. Critically evaluate it; reuse only what helps:",
    "wave_c": "Compiler-validated peer skeleton: fill its residual holes now.",
}
REQUEST_KEYS = (
    "model", "messages", "max_tokens", "temperature", "top_p", "seed",
    "stop", "reasoning", "tools", "tool_choice",
)
CSV_FIELDS = (
    "source_wave", "source_task", "source_call_id", "problem", "direction",
    "model", "variant", "sample", "seed", "temperature", "reasoning",
    "response_id", "finish_reason", "warm_accepted", "warm_timed_out",
    "warm_duration_ms", "warm_message_count", "prompt_tokens",
    "completion_tokens", "total_tokens", "cost_usd", "latency_ms",
    "candidate_sha256", "error",
)


def sha(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def challenge_from_messages(messages: list[dict[str, Any]]) -> str:
    joined = "\n".join(str(message.get("content", "")) for message in messages)
    matches = re.findall(
        r"Pristine Lean challenge:\s*```(?:lean|lean4)?\s*\n(.*?)```",
        joined,
        flags=re.DOTALL | re.IGNORECASE,
    )
    if not matches:
        raise ValueError("request has no pristine Lean challenge block")
    return matches[-1].strip() + "\n"


def task_from_path(path: Path) -> str:
    for part in path.parts:
        if part.startswith(("stage3v1-", "stage3fill-")):
            return part
    return path.parent.name


def collect(root: Path, wave: str) -> list[dict[str, Any]]:
    marker = MARKERS[wave]
    records: dict[str, dict[str, Any]] = {}
    for transcript_path in sorted(root.rglob("transcript.json")):
        try:
            transcript = json.loads(transcript_path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        problem = str(transcript.get("problem_id", ""))
        if problem.startswith("rmo_"):
            continue
        for call in transcript.get("calls", []):
            request = call.get("request") or {}
            messages = request.get("messages") or []
            if marker not in "\n".join(str(m.get("content", "")) for m in messages):
                continue
            call_id = str(call.get("call_id", ""))
            if not call_id:
                continue
            challenge = challenge_from_messages(messages)
            model = str(request["model"])
            source_model = (
                "qwen/qwen3.5-flash-02-23"
                if model == "openai/gpt-oss-120b"
                else "openai/gpt-oss-120b"
            )
            replay_request = {
                key: copy.deepcopy(request[key]) for key in REQUEST_KEYS if key in request
            }
            records.setdefault(call_id, {
                "source_wave": wave,
                "source_task": task_from_path(transcript_path),
                "source_transcript": str(transcript_path.relative_to(root)),
                "source_call_id": call_id,
                "problem": problem,
                "direction": f"{source_model} -> {model}",
                "base_imports": pristine_import_block(challenge),
                "challenge": challenge,
                "request": replay_request,
                "request_sha256": sha(json.dumps(replay_request, sort_keys=True)),
            })
    return list(records.values())


def balanced_sample(records: list[dict[str, Any]], count: int) -> list[dict[str, Any]]:
    strata: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for record in records:
        strata[(record["problem"], record["direction"])].append(record)
    for values in strata.values():
        values.sort(key=lambda row: sha(row["source_call_id"]))
    selected: list[dict[str, Any]] = []
    keys = sorted(strata)
    while len(selected) < count:
        progressed = False
        for key in keys:
            if strata[key] and len(selected) < count:
                selected.append(strata[key].pop(0))
                progressed = True
        if not progressed:
            raise ValueError(f"only {len(selected)} packet requests available; need {count}")
    return selected


def prepare(wave_a_root: Path, wave_c_root: Path, output: Path) -> None:
    wave_a = balanced_sample(collect(wave_a_root, "wave_a"), 60)
    wave_c = sorted(collect(wave_c_root, "wave_c"), key=lambda row: row["source_call_id"])
    if len(wave_c) != 25:
        raise ValueError(f"expected 25 non-rmo Wave C peer_fill requests, found {len(wave_c)}")
    records = wave_c + wave_a
    manifest = {
        "schema_version": 1,
        "experiment": "packet-replay-wave-a-c-v1",
        "created_at": datetime.now(UTC).isoformat(),
        "selection": {
            "wave_c": "all non-rmo peer_fill requests",
            "wave_a": "60 non-rmo packet requests, deterministic round-robin over problem and direction",
            "rmo_excluded": True,
            "samples_per_variant": 2,
            "variants": ["with_packet", "without_packet"],
            "budget_cap_usd": 5.0,
        },
        "records": records,
    }
    atomic_json(output, manifest)
    print(json.dumps({"manifest": str(output), "records": len(records),
                      "jobs": len(records) * 4}, sort_keys=True))


def without_packet(messages: list[dict[str, Any]], marker: str) -> list[dict[str, Any]]:
    result = copy.deepcopy(messages)
    matches = 0
    for message in result:
        content = str(message.get("content", ""))
        position = content.find(marker)
        if position < 0:
            continue
        matches += 1
        cut = position
        while cut > 0 and content[cut - 1] == "\n":
            cut -= 1
        message["content"] = content[:cut].rstrip() + "\n"
    if matches != 1:
        raise ValueError(f"expected one packet block, found {matches}")
    return result


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=CSV_FIELDS)
        writer.writeheader()
        writer.writerows(sorted(rows, key=lambda row: (
            row["source_wave"], row["source_call_id"], row["variant"], row["sample"]
        )))
    temporary.replace(path)


async def run(manifest_path: Path, output_dir: Path, concurrency: int) -> None:
    manifest = json.loads(manifest_path.read_text())
    jobs: list[tuple[dict[str, Any], str, int]] = []
    for record in manifest["records"]:
        for variant in ("with_packet", "without_packet"):
            for sample in (1, 2):
                jobs.append((record, variant, sample))

    output_dir.mkdir(parents=True, exist_ok=True)
    events = EventLogger(
        output_dir / "events.jsonl", problem_id="packet-replay",
        secrets=(os.environ.get("OPENROUTER_API_KEY", ""),),
    )
    budget = BudgetLedger(5.0)
    llm = LLMClient(api_key=os.environ.get("OPENROUTER_API_KEY", ""),
                    budget=budget, events=events)
    lean = LeanClient(image=LEAN_IMAGE, events=events, session_id=uuid.uuid4().hex,
                      timeout_s=120, base_imports="import Mathlib")
    rows: list[dict[str, Any]] = []
    csv_path = output_dir / "packet-replay.csv"
    lock = asyncio.Lock()
    queue: asyncio.Queue[tuple[dict[str, Any], str, int]] = asyncio.Queue()
    for job in jobs:
        queue.put_nowait(job)
    failure: list[str] = []

    async def worker() -> None:
        while not failure:
            try:
                record, variant, sample = queue.get_nowait()
            except asyncio.QueueEmpty:
                return
            request = copy.deepcopy(record["request"])
            if variant == "without_packet":
                request["messages"] = without_packet(
                    request["messages"], MARKERS[record["source_wave"]]
                )
            started = time.monotonic()
            error = ""
            response = None
            check = None
            candidate_hash = ""
            try:
                kwargs = {key: request[key] for key in REQUEST_KEYS if key in request}
                response = await llm.complete(timeout_s=420, **kwargs)
                candidate = canonicalize_imports(
                    _extract_lean(response.content, fallback=record["challenge"]),
                    record["base_imports"],
                )
                candidate_hash = sha(candidate)
                if pristine_import_block(record["challenge"]) != "import Mathlib":
                    raise ValueError("non-Mathlib import slipped past replay exclusion")
                check = await lean.check_file(candidate, timeout_s=120)
            except BudgetExceeded:
                queue.task_done()
                return
            except Exception as exc:  # task policy is fail closed, without paid retries
                error = f"{type(exc).__name__}: {exc}"[:500]
                failure.append(error)
            usage = dict(response.usage) if response else {}
            row = {
                "source_wave": record["source_wave"],
                "source_task": record["source_task"],
                "source_call_id": record["source_call_id"],
                "problem": record["problem"],
                "direction": record["direction"],
                "model": request["model"],
                "variant": variant,
                "sample": sample,
                "seed": request.get("seed", ""),
                "temperature": request.get("temperature", ""),
                "reasoning": json.dumps(request.get("reasoning"), sort_keys=True),
                "response_id": response.id if response else "",
                "finish_reason": response.finish_reason if response else "",
                "warm_accepted": check.accepted if check else "",
                "warm_timed_out": check.timed_out if check else "",
                "warm_duration_ms": check.duration_ms if check else "",
                "warm_message_count": len(check.messages) if check else "",
                "prompt_tokens": usage.get("prompt_tokens", ""),
                "completion_tokens": usage.get("completion_tokens", ""),
                "total_tokens": usage.get("total_tokens", ""),
                "cost_usd": usage.get("cost", ""),
                "latency_ms": round((time.monotonic() - started) * 1000),
                "candidate_sha256": candidate_hash,
                "error": error,
            }
            async with lock:
                rows.append(row)
                write_csv(csv_path, rows)
                atomic_json(output_dir / "status.json", {
                    "experiment": manifest["experiment"],
                    "updated_at": datetime.now(UTC).isoformat(),
                    "planned_jobs": len(jobs),
                    "completed_rows": len(rows),
                    "queued_jobs": queue.qsize(),
                    "budget": budget.snapshot().__dict__,
                    "failure": failure[0] if failure else None,
                })
            queue.task_done()

    try:
        await asyncio.gather(*(worker() for _ in range(concurrency)))
    finally:
        lean.close()
        await llm.aclose()
    status = "failed" if failure else ("complete" if not queue.qsize() else "budget_cap")
    atomic_json(output_dir / "result.json", {
        "experiment": manifest["experiment"],
        "status": status,
        "finished_at": datetime.now(UTC).isoformat(),
        "planned_jobs": len(jobs),
        "completed_rows": len(rows),
        "remaining_jobs": queue.qsize(),
        "budget": budget.snapshot().__dict__,
        "failure": failure[0] if failure else None,
    })
    if failure:
        raise RuntimeError(failure[0])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    prep = sub.add_parser("prepare")
    prep.add_argument("--wave-a-root", type=Path, required=True)
    prep.add_argument("--wave-c-root", type=Path, required=True)
    prep.add_argument("--output", type=Path, required=True)
    execute = sub.add_parser("run")
    execute.add_argument("--manifest", type=Path, required=True)
    execute.add_argument("--output-dir", type=Path, required=True)
    execute.add_argument("--concurrency", type=int, default=4)
    args = parser.parse_args()
    if args.command == "prepare":
        prepare(args.wave_a_root, args.wave_c_root, args.output)
    else:
        if not 1 <= args.concurrency <= 8:
            parser.error("concurrency must be between 1 and 8")
        asyncio.run(run(args.manifest, args.output_dir, args.concurrency))


if __name__ == "__main__":
    main()
