#!/usr/bin/env python3
"""Prepare, run, and summarize the fixed packet-content replay variants."""

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
from collections import Counter, defaultdict
from datetime import datetime, timezone
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


PACKET_MARKER = "Compiler-validated peer skeleton: fill its residual holes now."
ORIGINAL_INSTRUCTION = (
    "Preserve its compiling declarations and helper proofs. Replace every explicit `sorry` "
    "with complete Lean code; return one complete file without `sorry`. Do not critique, "
    "summarize, or restart from scratch unless Lean diagnostics prove the skeleton unusable."
)
LEMMAS_INSTRUCTION = (
    "Verified helper facts from an independent solver; use any that help, ignore the rest."
)
SKELETON_START = "Compiling skeleton:\n"
SKELETON_END = "\n\nResidual Lean goals and diagnostics:"
VARIANTS = ("lemmas_only", "prefix_cap3")
REQUEST_KEYS = (
    "model", "messages", "max_tokens", "temperature", "top_p", "seed",
    "stop", "reasoning", "tools", "tool_choice",
)
CSV_FIELDS = (
    "source_wave", "source_task", "source_call_id", "problem", "direction",
    "model", "variant", "lemmas_only_empty", "sample", "seed", "temperature",
    "reasoning", "response_id", "finish_reason", "warm_accepted",
    "warm_timed_out", "warm_duration_ms", "warm_message_count", "prompt_tokens",
    "completion_tokens", "total_tokens", "cost_usd", "latency_ms",
    "candidate_sha256", "error",
)


def sha(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def atomic_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def packet_from_messages(messages: list[dict[str, Any]]) -> str:
    matches = []
    for message in messages:
        content = str(message.get("content", ""))
        position = content.find(PACKET_MARKER)
        if position >= 0:
            matches.append(content[position:].strip())
    if len(matches) != 1:
        raise ValueError(f"expected one progress packet, found {len(matches)}")
    packet = matches[0]
    if packet.count(SKELETON_START) != 1 or packet.count(SKELETON_END) != 1:
        raise ValueError("packet does not have one delimited compiling skeleton")
    if packet.count(ORIGINAL_INSTRUCTION) != 1:
        raise ValueError("packet instruction differs from the frozen request")
    return packet


def skeleton_from_packet(packet: str) -> str:
    return packet.split(SKELETON_START, 1)[1].split(SKELETON_END, 1)[0]


def replace_skeleton(packet: str, skeleton: str) -> str:
    before, rest = packet.split(SKELETON_START, 1)
    _, after = rest.split(SKELETON_END, 1)
    return before + SKELETON_START + skeleton.rstrip() + SKELETON_END + after


def declaration_names(source: str) -> set[str]:
    return set(re.findall(
        r"(?m)^\s*(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)", source
    ))


def declaration_blocks(skeleton: str) -> list[str]:
    """Return complete top-level declarations from the skeleton."""
    lines = skeleton.splitlines()
    starts = [
        index for index, line in enumerate(lines)
        if re.match(r"^(?:theorem|lemma|def|abbrev)\s+", line)
    ]
    blocks = []
    for position, start in enumerate(starts):
        end = starts[position + 1] if position + 1 < len(starts) else len(lines)
        block = "\n".join(lines[start:end]).rstrip()
        if "sorry" not in block:
            blocks.append(block)
    return blocks


def have_blocks(skeleton: str) -> list[str]:
    """Extract complete theorem-local `have` blocks, preserving dependencies and order."""
    lines = skeleton.splitlines()
    results = []
    index = 0
    while index < len(lines):
        match = re.match(r"^(\s+)have\s+[^:]+\s*:", lines[index])
        if not match:
            index += 1
            continue
        indent = len(match.group(1).expandtabs(2))
        end = index + 1
        while end < len(lines):
            line = lines[end]
            if line.strip() and not line.lstrip().startswith("--"):
                next_indent = len(line) - len(line.lstrip())
                if next_indent <= indent:
                    break
            end += 1
        block_lines = lines[index:end]
        while len(block_lines) > 1 and (
            not block_lines[-1].strip() or block_lines[-1].lstrip().startswith("--")
        ):
            block_lines.pop()
        block = "\n".join(block_lines).rstrip()
        if ":=" in block and "sorry" not in block:
            results.append(block)
        index = max(end, index + 1)
    return results


def complete_helpers(skeleton: str, challenge: str) -> list[str]:
    challenge_names = declaration_names(challenge)
    helpers = []
    for block in declaration_blocks(skeleton):
        match = re.match(r"^(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)", block)
        if match and match.group(1) not in challenge_names:
            helpers.append(block)
    helpers.extend(have_blocks(skeleton))
    return helpers


def target_header_end(lines: list[str]) -> int:
    """Find the end of the last theorem header preceding the skeleton's hole."""
    hole = next((i for i, line in enumerate(lines) if re.search(r"\bsorry\b", line)), len(lines))
    starts = [i for i, line in enumerate(lines[:hole]) if re.match(r"^theorem\s+", line)]
    if not starts:
        raise ValueError("skeleton has no theorem before its hole")
    start = starts[-1]
    for index in range(start, hole):
        if re.search(r":=\s*by\s*$", lines[index]):
            return index
    raise ValueError("target theorem header has no `:= by`")


def original_prefix_line_count(skeleton: str) -> int:
    lines = skeleton.splitlines()
    header_end = target_header_end(lines)
    hole = next((i for i in range(header_end + 1, len(lines)) if re.search(r"\bsorry\b", lines[i])), len(lines))
    return hole - header_end - 1


def capped_skeleton(skeleton: str) -> str:
    lines = skeleton.splitlines()
    header_end = target_header_end(lines)
    hole = next(
        (i for i in range(header_end + 1, len(lines)) if re.search(r"\bsorry\b", lines[i])),
        len(lines),
    )
    body = lines[header_end + 1:hole][:3]
    indent = "  "
    for line in body:
        if line.strip():
            indent = line[:len(line) - len(line.lstrip())] or "  "
            break
    return "\n".join(lines[:header_end + 1] + body + [indent + "all_goals sorry"])


def transformed_packets(record: dict[str, Any]) -> tuple[dict[str, str], list[str], int]:
    packet = packet_from_messages(record["request"]["messages"])
    skeleton = skeleton_from_packet(packet)
    helpers = complete_helpers(skeleton, record["challenge"])
    lemmas = ""
    if helpers:
        lemmas = replace_skeleton(packet, "\n\n".join(helpers)).replace(
            ORIGINAL_INSTRUCTION, LEMMAS_INSTRUCTION, 1
        )
    cap3 = replace_skeleton(packet, capped_skeleton(skeleton))
    return {"lemmas_only": lemmas, "prefix_cap3": cap3}, helpers, original_prefix_line_count(skeleton)


def prepare(source_records: Path, k8_csv: Path, output: Path) -> None:
    source = json.loads(source_records.read_text())
    with k8_csv.open(newline="") as handle:
        k8_rows = list(csv.DictReader(handle))
    ids = sorted({row["source_call_id"] for row in k8_rows})
    if len(ids) != 47:
        raise ValueError(f"expected 47 K=8 source states, found {len(ids)}")
    by_id = {record["source_call_id"]: record for record in source["records"]}
    if set(ids) != set(by_id):
        raise ValueError("source records do not exactly match K=8 call IDs")
    records = []
    for call_id in ids:
        record = copy.deepcopy(by_id[call_id])
        packets, helpers, prefix_count = transformed_packets(record)
        record.update({
            "original_prefix_line_count": prefix_count,
            "complete_helpers_count": len(helpers),
            "complete_helpers": helpers,
            "lemmas_only_empty": not helpers,
            "transformed_packet_texts": packets,
        })
        records.append(record)
    waves = Counter(record["source_wave"] for record in records)
    if waves != {"wave_c": 25, "wave_d": 22}:
        raise ValueError(f"wrong frozen wave composition: {dict(waves)}")
    manifest = {
        "schema_version": 1,
        "experiment": "packet-content-replay-variants-k8-v1",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "selection": {
            "source": "exact 47 source_call_id states in packet-replay-k8.csv",
            "wave_c_states": 25,
            "wave_d_states": 22,
            "variants": list(VARIANTS),
            "samples_per_variant": 8,
            "budget_cap_usd": 5.0,
            "paid_retries": False,
        },
        "records": records,
    }
    atomic_json(output, manifest)
    print(json.dumps({
        "manifest": str(output), "states": len(records), "jobs": len(records) * 16,
        "lemmas_only_empty_states": sum(record["lemmas_only_empty"] for record in records),
    }, sort_keys=True))


def messages_for(record: dict[str, Any], variant: str) -> list[dict[str, Any]]:
    result = copy.deepcopy(record["request"]["messages"])
    transformed = record["transformed_packet_texts"][variant]
    matches = 0
    for message in result:
        content = str(message.get("content", ""))
        position = content.find(PACKET_MARKER)
        if position < 0:
            continue
        matches += 1
        cut = position
        while cut and content[cut - 1] == "\n":
            cut -= 1
        prefix = content[:cut].rstrip()
        message["content"] = prefix + ("\n\n" + transformed if transformed else "") + "\n"
    if matches != 1:
        raise ValueError(f"expected one packet block, found {matches}")
    return result


def canonicalize_for_replay(source: str, base_imports: str) -> str:
    body = "\n".join(
        line for line in source.splitlines() if not line.lstrip().startswith("import ")
    ).lstrip("\n")
    return base_imports.rstrip() + "\n\n" + body + ("\n" if body else "")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=CSV_FIELDS)
        writer.writeheader()
        writer.writerows(sorted(rows, key=lambda row: (
            row["source_wave"], row["source_call_id"], row["variant"], int(row["sample"]),
        )))
    temporary.replace(path)


def job_key(row: dict[str, Any]) -> tuple[str, str, str]:
    return str(row["source_call_id"]), str(row["variant"]), str(row["sample"])


def prior_checkpoint(output_dir: Path) -> tuple[list[dict[str, Any]], float]:
    rows = []
    csv_path = output_dir / "packet-replay-variants.csv"
    if csv_path.exists():
        with csv_path.open(newline="") as handle:
            # Every dispatched request is terminal, including provider/local error rows.
            rows = list(csv.DictReader(handle))
    prior_spend = 0.0
    result_path = output_dir / "result.json"
    if result_path.exists():
        result = json.loads(result_path.read_text())
        prior_spend = float(result.get(
            "cumulative_spent_usd", result.get("budget", {}).get("spent_usd", 0),
        ))
    return rows, prior_spend


async def run(manifest_path: Path, output_dir: Path, concurrency: int) -> None:
    manifest = json.loads(manifest_path.read_text())
    all_jobs = [
        (record, variant, sample)
        for record in manifest["records"]
        for variant in VARIANTS
        for sample in range(1, 9)
    ]
    if len(all_jobs) != 752:
        raise ValueError(f"expected 752 jobs, found {len(all_jobs)}")
    output_dir.mkdir(parents=True, exist_ok=True)
    rows, prior_spend = prior_checkpoint(output_dir)
    completed = {job_key(row) for row in rows}
    jobs = [job for job in all_jobs if (
        job[0]["source_call_id"], job[1], str(job[2]),
    ) not in completed]
    remaining_budget = 5.0 - prior_spend
    if remaining_budget <= 0:
        raise BudgetExceeded("the variants replay's cumulative $5 cap is exhausted")
    events = EventLogger(
        output_dir / "events.jsonl", problem_id="packet-replay-variants",
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
    provider_failure: list[str] = []
    csv_path = output_dir / "packet-replay-variants.csv"

    def budget_status() -> dict[str, Any]:
        snapshot = budget.snapshot()
        return {
            "limit_usd": 5.0,
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

    async def worker() -> None:
        while not provider_failure:
            try:
                record, variant, sample = queue.get_nowait()
            except asyncio.QueueEmpty:
                return
            request = copy.deepcopy(record["request"])
            request["messages"] = messages_for(record, variant)
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
                check = await lean_for(record["base_imports"]).check_file(candidate, timeout_s=120)
            except BudgetExceeded:
                queue.task_done()
                return
            except Exception as exc:
                error = f"{type(exc).__name__}: {exc}"[:500]
                # Provider failures stop new dispatch. Paid responses with local warm-check
                # errors remain terminal but do not trigger any retry.
                if response is None:
                    provider_failure.append(error)
            usage = dict(response.usage) if response else {}
            row = {
                "source_wave": record["source_wave"],
                "source_task": record["source_task"],
                "source_call_id": record["source_call_id"],
                "problem": record["problem"],
                "direction": record["direction"],
                "model": request["model"],
                "variant": variant,
                "lemmas_only_empty": record["lemmas_only_empty"] if variant == "lemmas_only" else False,
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
                    "updated_at": datetime.now(timezone.utc).isoformat(),
                    "planned_jobs": len(all_jobs),
                    "completed_rows": len(rows),
                    "queued_jobs": queue.qsize(),
                    "budget": budget_status(),
                    "failure": provider_failure[0] if provider_failure else None,
                })
            queue.task_done()

    try:
        await asyncio.gather(*(worker() for _ in range(concurrency)))
    finally:
        for lean in lean_clients.values():
            lean.close()
        await llm.aclose()
    status = "failed" if provider_failure else (
        "complete" if len(rows) == len(all_jobs) else "budget_cap"
    )
    atomic_json(output_dir / "result.json", {
        "experiment": manifest["experiment"],
        "status": status,
        "finished_at": datetime.now(timezone.utc).isoformat(),
        "planned_jobs": len(all_jobs),
        "completed_rows": len(rows),
        "error_rows": sum(bool(row.get("error")) for row in rows),
        "remaining_jobs": len(all_jobs) - len(rows),
        "budget": budget_status(),
        "cumulative_spent_usd": budget_status()["spent_usd"],
        "failure": provider_failure[0] if provider_failure else None,
    })
    if provider_failure:
        raise RuntimeError(provider_failure[0])


def truth(value: str) -> bool:
    return value.lower() == "true"


def rates_by_state(rows: list[dict[str, str]]) -> dict[tuple[str, str], float]:
    grouped: dict[tuple[str, str], list[bool]] = defaultdict(list)
    for row in rows:
        grouped[(row["source_call_id"], row["variant"])].append(
            truth(row.get("warm_accepted", "")) and not bool(row.get("error"))
        )
    return {key: sum(values) / len(values) for key, values in grouped.items()}


def summarize(variants_csv: Path, k8_csv: Path, output: Path) -> None:
    with variants_csv.open(newline="") as handle:
        rows = list(csv.DictReader(handle))
    with k8_csv.open(newline="") as handle:
        k8 = list(csv.DictReader(handle))
    if len(rows) != 752:
        raise ValueError(f"summary requires 752 variant rows, found {len(rows)}")
    rates = rates_by_state(rows)
    baseline = rates_by_state([row for row in k8 if row["variant"] == "without_packet"])
    lines = [
        "# Packet-content replay variants", "",
        "Warm-pass outcomes count provider refusals and local-check errors as failures. "
        "Differences are paired at the request-state level against the existing K=8 "
        "`without_packet` rate for the same 47 states.", "",
        "| Variant | Warm passes | Request-level mean | Paired difference | States up/down/tied |",
        "|---|---:|---:|---:|---:|",
    ]
    for variant in VARIANTS:
        subset = [row for row in rows if row["variant"] == variant]
        ids = sorted({row["source_call_id"] for row in subset})
        diffs = [rates[(call_id, variant)] - baseline[(call_id, "without_packet")] for call_id in ids]
        up, down = sum(x > 0 for x in diffs), sum(x < 0 for x in diffs)
        passed = sum(truth(row.get("warm_accepted", "")) and not row.get("error") for row in subset)
        lines.append(
            f"| `{variant}` | {passed}/{len(subset)} | "
            f"{sum(rates[(call_id, variant)] for call_id in ids) / len(ids):.3f} | "
            f"{sum(diffs) / len(diffs):+.3f} | {up}/{down}/{len(ids)-up-down} |"
        )
    lines += ["", "## Splits", ""]
    for dimension, key_name in (("Wave", "source_wave"), ("Receiving model", "model")):
        lines += [f"### {dimension}", "", "| Group | Variant | Warm passes | Request-level mean | Paired difference | States up/down/tied |", "|---|---|---:|---:|---:|---:|"]
        groups = sorted({row[key_name] for row in rows})
        meta = {row["source_call_id"]: row for row in rows}
        for group in groups:
            ids = sorted(call_id for call_id, row in meta.items() if row[key_name] == group)
            for variant in VARIANTS:
                subset = [row for row in rows if row[key_name] == group and row["variant"] == variant]
                diffs = [rates[(call_id, variant)] - baseline[(call_id, "without_packet")] for call_id in ids]
                up, down = sum(x > 0 for x in diffs), sum(x < 0 for x in diffs)
                passed = sum(truth(row.get("warm_accepted", "")) and not row.get("error") for row in subset)
                lines.append(
                    f"| {group} | `{variant}` | {passed}/{len(subset)} | "
                    f"{sum(rates[(call_id, variant)] for call_id in ids) / len(ids):.3f} | "
                    f"{sum(diffs) / len(diffs):+.3f} | {up}/{down}/{len(ids)-up-down} |"
                )
        lines.append("")
    output.write_text("\n".join(lines).rstrip() + "\n")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    prep = sub.add_parser("prepare")
    prep.add_argument("--source-records", type=Path, required=True)
    prep.add_argument("--k8-csv", type=Path, required=True)
    prep.add_argument("--output", type=Path, required=True)
    execute = sub.add_parser("run")
    execute.add_argument("--manifest", type=Path, required=True)
    execute.add_argument("--output-dir", type=Path, required=True)
    execute.add_argument("--concurrency", type=int, default=8)
    report = sub.add_parser("summarize")
    report.add_argument("--variants-csv", type=Path, required=True)
    report.add_argument("--k8-csv", type=Path, required=True)
    report.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "prepare":
        prepare(args.source_records, args.k8_csv, args.output)
    elif args.command == "run":
        if not 1 <= args.concurrency <= 8:
            parser.error("concurrency must be between 1 and 8")
        asyncio.run(run(args.manifest, args.output_dir, args.concurrency))
    else:
        summarize(args.variants_csv, args.k8_csv, args.output)


if __name__ == "__main__":
    main()
