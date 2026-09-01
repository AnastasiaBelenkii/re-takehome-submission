#!/usr/bin/env python3
"""Replay one archived Qwen call with thinking disabled."""

from __future__ import annotations

import argparse
import asyncio
import json
import os
import uuid
from pathlib import Path

from dotenv import load_dotenv

from baselines.simple_agent import _extract_lean
from collaboration_engine_v2.tactics import (
    canonicalize_imports,
    required_declarations_present,
)
from re_harness.artifacts import atomic_write_json, atomic_write_text
from re_harness.budget import BudgetLedger
from re_harness.events import EventLogger, read_events
from re_harness.lean import LeanClient
from re_harness.llm import LLMClient
from scripts.launch_online_microcell import LEAN_IMAGE


CONFIRMATION = "I_UNDERSTAND_THIS_LAUNCHES_ONE_PAID_QWEN_PROBE"


async def run_probe(transcript: Path, call_id: str, output: Path) -> dict[str, object]:
    payload = json.loads(transcript.read_text())
    matches = [call for call in payload["calls"] if call.get("call_id") == call_id]
    if len(matches) != 1:
        raise ValueError("call id must identify exactly one archived call")
    archived = matches[0]
    request = archived["request"]
    if request.get("model") != "qwen/qwen3.5-flash-02-23":
        raise ValueError("probe only permits the audited Qwen model")
    if output.exists():
        raise ValueError("output directory already exists")
    output.mkdir(parents=True)

    api_key = os.environ.get("OPENROUTER_API_KEY", "").strip()
    if not api_key:
        raise RuntimeError("OPENROUTER_API_KEY is not configured")
    events_path = output / "events.jsonl"
    events = EventLogger(events_path, problem_id="qwen-reasoning-probe", secrets=(api_key,))
    llm = LLMClient(api_key=api_key, budget=BudgetLedger(0.05), events=events)
    lean = LeanClient(
        image=LEAN_IMAGE,
        events=events,
        session_id=uuid.uuid4().hex,
        timeout_s=120,
    )
    try:
        response = await llm.complete(
            model=request["model"],
            messages=request["messages"],
            max_tokens=request["max_tokens"],
            temperature=request.get("temperature"),
            seed=request.get("seed"),
            stop=request.get("stop"),
            reasoning={"effort": "none"},
        )
        candidate = canonicalize_imports(_extract_lean(response.content, fallback=""))
        structurally_complete = required_declarations_present(
            "import Mathlib\n\ntheorem putnam_2020_a2 (k : ℕ) : "
            "(∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) = 4 ^ k := by sorry\n",
            candidate,
        )
        check = await lean.check_file(candidate) if structurally_complete else None
        llm_event = next(
            event for event in reversed(read_events(events_path))
            if event.get("event") == "llm_response"
        )
        summary: dict[str, object] = {
            "schema_version": 1,
            "archived_call_id": call_id,
            "change": {"reasoning": {"effort": "none"}},
            "control": {
                "finish_reason": archived["response"]["choices"][0]["finish_reason"],
                "completion_tokens": archived["response"]["usage"]["completion_tokens"],
                "latency_ms": archived["latency_ms"],
                "cost_usd": archived["actual_cost_usd"],
            },
            "probe": {
                "finish_reason": response.finish_reason,
                "completion_tokens": response.usage.get("completion_tokens"),
                "latency_ms": llm_event.get("latency_ms"),
                "cost_usd": llm_event.get("actual_cost_usd"),
                "content_chars": len(response.content),
                "contains_required_theorem": "theorem putnam_2020_a2" in response.content,
                "structurally_complete": structurally_complete,
                "warm_lean_accepted": bool(check and check.accepted),
                "warm_lean_timed_out": bool(check and check.timed_out),
                "warm_lean_message_count": len(check.messages) if check else None,
            },
        }
        atomic_write_text(output / "candidate.lean", candidate)
        atomic_write_json(output / "summary.json", summary)
        return summary
    finally:
        lean.close()
        await llm.aclose()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--transcript", type=Path, required=True)
    parser.add_argument("--call-id", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--confirm-paid-probe")
    args = parser.parse_args()
    if args.confirm_paid_probe != CONFIRMATION:
        raise SystemExit(f"confirmation required: {CONFIRMATION}")
    load_dotenv(Path(__file__).resolve().parents[1] / ".env", override=False)
    summary = asyncio.run(run_probe(args.transcript, args.call_id, args.output))
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
