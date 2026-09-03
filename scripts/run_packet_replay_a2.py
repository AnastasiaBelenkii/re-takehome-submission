#!/usr/bin/env python3
"""Run an explicit, resumable shard of the A2 packet replay.

This launcher deliberately consumes a frozen manifest.  It never retries a paid
request, and it preserves each challenge's original import block for warm Lean.
"""

from __future__ import annotations

import argparse
import asyncio
import copy
import csv
import hashlib
import json
import os
import sys
import time
import uuid
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "src"), str(ROOT)]

from baselines.simple_agent import _extract_lean
from collaboration_engine_v2.experiment import LEAN_IMAGE
from re_harness.budget import BudgetExceeded, BudgetLedger
from re_harness.events import EventLogger
from re_harness.lean import LeanClient
from re_harness.llm import LLMClient
MARKERS = {
    "wave_a": "Evidence from an independent solver. Critically evaluate it; reuse only what helps:",
    "wave_c": "Compiler-validated peer skeleton: fill its residual holes now.",
    "wave_d": "Compiler-validated peer skeleton: fill its residual holes now.",
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
    return hashlib.sha256(value.encode()).hexdigest()


def canonicalize_for_replay(source: str, base_imports: str) -> str:
    """Match the import-fix behavior without depending on the runtime commit."""
    body = "\n".join(
        line for line in source.splitlines()
        if not line.lstrip().startswith("import ")
    ).lstrip("\n")
    return base_imports.rstrip() + "\n\n" + body + (
        "\n" if body and not body.endswith("\n") else ""
    )


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


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
        while cut and content[cut - 1] == "\n":
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
            row["source_wave"], row["source_call_id"], row["variant"],
            int(row["sample"]),
        )))
    temporary.replace(path)


def job_key(row: dict[str, Any]) -> tuple[str, str, str]:
    return str(row["source_call_id"]), str(row["variant"]), str(row["sample"])


def prior_checkpoint(output_dir: Path) -> tuple[list[dict[str, Any]], float]:
    rows: list[dict[str, Any]] = []
    csv_path = output_dir / "packet-replay.csv"
    if csv_path.exists():
        with csv_path.open(newline="") as handle:
            # A paid request is terminal even if local post-processing failed.
            # Keeping error rows prevents a resume from dispatching it again.
            rows = list(csv.DictReader(handle))
    prior_spend = 0.0
    result_path = output_dir / "result.json"
    if result_path.exists():
        result = json.loads(result_path.read_text())
        prior_spend = float(result.get(
            "cumulative_spent_usd", result.get("budget", {}).get("spent_usd", 0)
        ))
    return rows, prior_spend


async def run(manifest_path: Path, output_dir: Path, concurrency: int) -> None:
    manifest = json.loads(manifest_path.read_text())
    samples = [int(value) for value in manifest["samples"]]
    all_jobs = [
        (record, variant, sample)
        for record in manifest["records"]
        for variant in ("with_packet", "without_packet")
        for sample in samples
    ]
    output_dir.mkdir(parents=True, exist_ok=True)
    rows, prior_spend = prior_checkpoint(output_dir)
    completed = {job_key(row) for row in rows}
    jobs = [job for job in all_jobs if (
        job[0]["source_call_id"], job[1], str(job[2])
    ) not in completed]
    limit = float(manifest["budget_cap_usd"])
    remaining_budget = limit - prior_spend
    if remaining_budget <= 0:
        raise BudgetExceeded("this shard's cumulative budget cap is exhausted")

    events = EventLogger(
        output_dir / "events.jsonl", problem_id="packet-replay-a2",
        secrets=(os.environ.get("OPENROUTER_API_KEY", ""),),
    )
    budget = BudgetLedger(remaining_budget)
    llm = LLMClient(
        api_key=os.environ.get("OPENROUTER_API_KEY", ""), budget=budget, events=events,
    )
    lean_clients: dict[str, LeanClient] = {}
    rows_lock = asyncio.Lock()
    queue: asyncio.Queue[tuple[dict[str, Any], str, int]] = asyncio.Queue()
    for job in jobs:
        queue.put_nowait(job)
    failure: list[str] = []
    csv_path = output_dir / "packet-replay.csv"

    def budget_status() -> dict[str, Any]:
        snapshot = budget.snapshot()
        return {
            "limit_usd": limit,
            "spent_usd": prior_spend + snapshot.spent_usd,
            "reserved_usd": snapshot.reserved_usd,
            "accounting_complete": snapshot.accounting_complete,
            "resume_prior_spend_usd": prior_spend,
        }

    def lean_for(imports: str) -> LeanClient:
        if imports not in lean_clients:
            lean_clients[imports] = LeanClient(
                image=LEAN_IMAGE, events=events, session_id=uuid.uuid4().hex,
                timeout_s=120, base_imports=imports,
            )
        return lean_clients[imports]

    async def recover_prior_postprocessing_errors() -> None:
        """Warm-check paid responses whose first launcher failed after receipt."""
        targets = {
            row.get("response_id"): row for row in rows
            if row.get("error", "").startswith("TypeError: canonicalize_imports")
            and row.get("response_id")
        }
        if not targets:
            return
        responses: dict[str, str] = {}
        events_path = output_dir / "events.jsonl"
        if events_path.exists():
            for line in events_path.read_text().splitlines():
                try:
                    event = json.loads(line)
                    response = event.get("response") or {}
                    response_id = str(response.get("id", ""))
                    if response_id in targets:
                        responses[response_id] = str(
                            response["choices"][0]["message"].get("content", "")
                        )
                except (KeyError, IndexError, TypeError, json.JSONDecodeError):
                    continue
        records = {record["source_call_id"]: record for record in manifest["records"]}
        for response_id, row in targets.items():
            if response_id not in responses:
                continue
            record = records[row["source_call_id"]]
            candidate = canonicalize_for_replay(
                _extract_lean(responses[response_id], fallback=record["challenge"]),
                record["base_imports"],
            )
            check = await lean_for(record["base_imports"]).check_file(candidate, timeout_s=120)
            row.update({
                "warm_accepted": check.accepted,
                "warm_timed_out": check.timed_out,
                "warm_duration_ms": check.duration_ms,
                "warm_message_count": len(check.messages),
                "candidate_sha256": sha(candidate),
                "error": "",
            })
        write_csv(csv_path, rows)

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
                candidate = canonicalize_for_replay(
                    _extract_lean(response.content, fallback=record["challenge"]),
                    record["base_imports"],
                )
                candidate_hash = sha(candidate)
                check = await lean_for(record["base_imports"]).check_file(
                    candidate, timeout_s=120
                )
            except BudgetExceeded:
                queue.task_done()
                return
            except Exception as exc:
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
            async with rows_lock:
                rows.append(row)
                write_csv(csv_path, rows)
                atomic_json(output_dir / "status.json", {
                    "experiment": manifest["experiment"],
                    "planned_jobs": len(all_jobs),
                    "completed_rows": len(rows),
                    "queued_jobs": queue.qsize(),
                    "budget": budget_status(),
                    "failure": failure[0] if failure else None,
                })
            queue.task_done()

    try:
        await recover_prior_postprocessing_errors()
        await asyncio.gather(*(worker() for _ in range(concurrency)))
    finally:
        for lean in lean_clients.values():
            lean.close()
        await llm.aclose()
    completed_rows = len(rows)
    status = "failed" if failure else (
        "complete" if completed_rows == len(all_jobs) else "budget_cap"
    )
    atomic_json(output_dir / "result.json", {
        "experiment": manifest["experiment"],
        "status": status,
        "planned_jobs": len(all_jobs),
        "completed_rows": completed_rows,
        "error_rows": sum(bool(row.get("error")) for row in rows),
        "remaining_jobs": len(all_jobs) - completed_rows,
        "budget": budget_status(),
        "cumulative_spent_usd": budget_status()["spent_usd"],
        "failure": failure[0] if failure else None,
    })
    if failure:
        raise RuntimeError(failure[0])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--concurrency", type=int, default=4)
    args = parser.parse_args()
    if not 1 <= args.concurrency <= 8:
        parser.error("concurrency must be between 1 and 8")
    asyncio.run(run(args.manifest, args.output_dir, args.concurrency))


if __name__ == "__main__":
    main()
