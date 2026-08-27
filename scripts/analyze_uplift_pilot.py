#!/usr/bin/env python3
"""Calculate the predeclared P-versus-D selection metrics from four valid bundles."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
for import_root in (ROOT / "src", ROOT):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from uplift_pilot.experiment import EXPECTED_CONDITIONS, EXPECTED_PROBLEMS


def _json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def _one_run(bundle: Path) -> Path:
    paths = list((bundle / "outputs").rglob("run.json"))
    if len(paths) != 1:
        raise ValueError(f"{bundle}: expected exactly one run.json, found {len(paths)}")
    return paths[0].parent


def summarize_bundle(bundle: Path) -> dict[str, Any]:
    validation = _json(bundle / "validation.json")
    if validation.get("valid") is not True:
        raise ValueError(f"{bundle}: bundle has not passed validation")
    provenance = _json(bundle / "provenance.json")
    condition_id = provenance.get("condition")
    if condition_id not in EXPECTED_CONDITIONS:
        raise ValueError(f"{bundle}: unknown condition {condition_id!r}")
    model, policy = EXPECTED_CONDITIONS[condition_id]
    if (provenance.get("model"), provenance.get("policy")) != (model, policy):
        raise ValueError(f"{bundle}: provenance condition/model/policy mismatch")
    run_dir = _one_run(bundle)
    passed: list[str] = []
    calls = prompt_tokens = completion_tokens = total_tokens = 0
    cost = wall_s = 0.0
    timeouts = restarts = planning_calls = 0
    restart_reasons: dict[str, int] = {}
    for problem_id in EXPECTED_PROBLEMS:
        result = _json(run_dir / problem_id / "result.json")
        transcript = _json(run_dir / problem_id / "transcript.json")
        if result.get("passed"):
            passed.append(problem_id)
        status = str(result.get("status", ""))
        comparator = result.get("comparator", {})
        if "timeout" in status or (isinstance(comparator, dict) and comparator.get("timed_out")):
            timeouts += 1
        calls_list = transcript.get("calls", [])
        if not isinstance(calls_list, list):
            raise ValueError(f"{problem_id}: transcript calls is not a list")
        calls += len(calls_list)
        for call in calls_list:
            usage = call.get("response", {}).get("usage", {}) if isinstance(call, dict) else {}
            if isinstance(usage, dict):
                prompt_tokens += int(usage.get("prompt_tokens") or 0)
                completion_tokens += int(usage.get("completion_tokens") or 0)
                total_tokens += int(usage.get("total_tokens") or 0)
        budget = result.get("budget", {})
        cost += float(budget.get("spent_usd", 0.0)) if isinstance(budget, dict) else 0.0
        wall_s += float(result.get("wall_s", 0.0))
        metadata = result.get("agent_metadata", {})
        if isinstance(metadata, dict):
            restarts += int(metadata.get("restarts") or 0)
            planning_calls += int(metadata.get("planning_calls") or 0)
            attempts = metadata.get("attempts", [])
            if isinstance(attempts, list):
                for attempt in attempts:
                    reason = attempt.get("restart_reason") if isinstance(attempt, dict) else None
                    if reason:
                        restart_reasons[str(reason)] = restart_reasons.get(str(reason), 0) + 1
    return {
        "condition": condition_id,
        "model": model,
        "policy": policy,
        "commit": provenance.get("git_commit"),
        "score": len(passed),
        "passed_problems": passed,
        "calls": calls,
        "prompt_tokens": prompt_tokens,
        "completion_tokens": completion_tokens,
        "total_tokens": total_tokens,
        "cost_usd": round(cost, 10),
        "wall_s": round(wall_s, 3),
        "timeouts": timeouts,
        "restarts": restarts,
        "planning_calls": planning_calls,
        "restart_reasons": restart_reasons,
        "bundle": str(bundle.resolve()),
    }


def analyze(bundles: list[Path]) -> dict[str, Any]:
    conditions = {summary["condition"]: summary for summary in map(summarize_bundle, bundles)}
    if set(conditions) != set(EXPECTED_CONDITIONS) or len(bundles) != 4:
        raise ValueError(f"expected one valid bundle for each condition: {sorted(EXPECTED_CONDITIONS)}")
    policies = {}
    for policy, qwen_id, gpt_id in (("P", "qwen-p", "gpt-p"), ("D", "qwen-d", "gpt-d")):
        qwen, gpt = conditions[qwen_id], conditions[gpt_id]
        qwen_passed, gpt_passed = set(qwen["passed_problems"]), set(gpt["passed_problems"])
        complementarity = {}
        for problem_id in EXPECTED_PROBLEMS:
            state = (
                "both" if problem_id in qwen_passed and problem_id in gpt_passed
                else "qwen_only" if problem_id in qwen_passed
                else "gpt_only" if problem_id in gpt_passed
                else "neither"
            )
            complementarity[problem_id] = state
        policies[policy] = {
            "model_scores": {qwen["model"]: qwen["score"], gpt["model"]: gpt["score"]},
            "sum_solo_scores": qwen["score"] + gpt["score"],
            "virtual_union_score": len(qwen_passed | gpt_passed),
            "virtual_union_problems": sorted(qwen_passed | gpt_passed),
            "complementarity": complementarity,
            "calls": qwen["calls"] + gpt["calls"],
            "prompt_tokens": qwen["prompt_tokens"] + gpt["prompt_tokens"],
            "completion_tokens": qwen["completion_tokens"] + gpt["completion_tokens"],
            "total_tokens": qwen["total_tokens"] + gpt["total_tokens"],
            "cost_usd": round(qwen["cost_usd"] + gpt["cost_usd"], 10),
            "wall_s": round(qwen["wall_s"] + gpt["wall_s"], 3),
            "timeouts": qwen["timeouts"] + gpt["timeouts"],
            "restarts": qwen["restarts"] + gpt["restarts"],
            "planning_calls": qwen["planning_calls"] + gpt["planning_calls"],
        }
    return {"schema_version": 1, "conditions": conditions, "policies": policies}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundles", nargs=4, type=Path)
    args = parser.parse_args(argv)
    try:
        report = analyze(args.bundles)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"analysis refused: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
