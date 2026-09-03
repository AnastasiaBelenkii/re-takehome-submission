#!/usr/bin/env python3
"""Recover warm-valid packet-conditioned candidates and re-run Comparator.

This is an offline audit utility: it makes no model calls and never edits the
original evaluator artifacts.  Candidate sources are reconstructed from the
immutable transcript and accepted only when their canonical SHA-256 matches an
attempt recorded by the agent.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import uuid
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "src"), str(ROOT)]

from baselines.simple_agent import _extract_lean
from collaboration_engine_v2.tactics import canonicalize_imports
from re_harness.config import DEFAULT_LEAN_IMAGE
from re_harness.lean import compare_solution
from re_harness.manifest import load_problem_set
from uplift_pilot.agent import _normalized_candidate


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


def _recover(task: Path) -> list[dict[str, Any]]:
    result_paths = list(task.rglob("result.json"))
    if len(result_paths) != 1:
        raise RuntimeError(f"{task}: expected one result.json, found {len(result_paths)}")
    problem_dir = result_paths[0].parent
    checkpoint = json.loads((problem_dir / "checkpoint.json").read_text())
    transcript = json.loads((problem_dir / "transcript.json").read_text())
    targets: dict[str, list[dict[str, Any]]] = {}
    for model, track in checkpoint["metadata"]["tracks"].items():
        for attempt in track.get("attempts", []):
            if attempt.get("peer_packet_used") and attempt.get("lean_accepted"):
                item = dict(attempt)
                item["model"] = model
                targets.setdefault(str(attempt["candidate_sha256"]), []).append(item)
    recovered: dict[str, str] = {}
    for call in transcript.get("calls", []):
        content = _response_content(call)
        if content is None:
            continue
        source = canonicalize_imports(_extract_lean(content, fallback=""))
        digest = _sha256(_normalized_candidate(source))
        if digest in targets:
            recovered[digest] = source
    rows = []
    for digest, attempts in targets.items():
        rows.append({
            "candidate_sha256": digest,
            "attempts": attempts,
            "source": recovered.get(digest),
            "recovered": digest in recovered,
            "problem_dir": problem_dir,
        })
    return rows


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tasks-root", type=Path, required=True)
    parser.add_argument("--task-name", action="append", default=[])
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--timeout-s", type=int, default=600)
    parser.add_argument("--image", default=DEFAULT_LEAN_IMAGE)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    summary: list[dict[str, Any]] = []
    tasks = (
        [args.tasks_root / name for name in args.task_name]
        if args.task_name else sorted(args.tasks_root.glob("*c1plus-fill-reserve"))
    )
    for task in tasks:
        problem_set = load_problem_set(task / "problem-set")
        if len(problem_set.problems) != 1:
            raise RuntimeError(f"{task}: expected one problem")
        spec = problem_set.problems[0]
        _description, challenge_path = problem_set.paths(spec)
        for recovered in _recover(task):
            row = {
                "task": task.name,
                "problem_id": spec.id,
                "candidate_sha256": recovered["candidate_sha256"],
                "attempts": recovered["attempts"],
                "recovered": recovered["recovered"],
            }
            candidate_out = args.out / task.name / recovered["candidate_sha256"]
            candidate_out.mkdir(parents=True)
            if recovered["source"] is None:
                row["error"] = "candidate source was not recoverable from transcript"
            else:
                source = recovered["source"]
                (candidate_out / "candidate.lean").write_text(source)
                verdict = compare_solution(
                    image=args.image,
                    session_id=uuid.uuid4().hex,
                    challenge=challenge_path.read_text(),
                    solution=source,
                    spec=spec,
                    timeout_s=args.timeout_s,
                )
                row["comparator"] = {
                    "passed": verdict.passed,
                    "exit_code": verdict.exit_code,
                    "timed_out": verdict.timed_out,
                    "duration_ms": verdict.duration_ms,
                    "output": verdict.output,
                }
            (candidate_out / "result.json").write_text(
                json.dumps(row, indent=2, sort_keys=True) + "\n"
            )
            summary.append(row)
            print(json.dumps({
                "task": row["task"],
                "candidate_sha256": row["candidate_sha256"],
                "recovered": row["recovered"],
                "passed": row.get("comparator", {}).get("passed"),
                "timed_out": row.get("comparator", {}).get("timed_out"),
                "duration_ms": row.get("comparator", {}).get("duration_ms"),
            }), flush=True)
    (args.out / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n"
    )
    return 0 if all(row.get("recovered") for row in summary) else 2


if __name__ == "__main__":
    raise SystemExit(main())
