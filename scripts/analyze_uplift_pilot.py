#!/usr/bin/env python3
"""Calculate the predeclared P-versus-D selection metrics from four valid bundles."""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
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


def _request_phase(call: Any) -> str | None:
    if not isinstance(call, dict):
        return None
    request = call.get("request", {})
    messages = request.get("messages", []) if isinstance(request, dict) else []
    if not isinstance(messages, list):
        return None
    contents = [
        str(message.get("content", ""))
        for message in messages
        if isinstance(message, dict)
    ]
    if any(content.startswith("Produce a short structured strategy memo") for content in contents):
        return "planning"
    for content in reversed(contents):
        match = re.search(r"(?:^|;) phase: ([a-z]+)(?:\n|$)", content)
        if match:
            return match.group(1)
    return None


def _response_content(call: Any) -> str:
    if not isinstance(call, dict):
        return ""
    response = call.get("response", {})
    try:
        content = response["choices"][0]["message"].get("content")
    except (KeyError, IndexError, TypeError):
        return ""
    return content if isinstance(content, str) else ""


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
    timeouts = agent_timeouts = comparator_timeouts = 0
    restarts = planning_calls = planning_memos_returned = planning_memos_injected = 0
    responses = cost_unknown = 0
    status_counts: Counter[str] = Counter()
    restart_reasons: dict[str, int] = {}
    problem_summaries: dict[str, dict[str, Any]] = {}
    for problem_id in EXPECTED_PROBLEMS:
        result = _json(run_dir / problem_id / "result.json")
        transcript = _json(run_dir / problem_id / "transcript.json")
        if result.get("passed"):
            passed.append(problem_id)
        status = str(result.get("status", ""))
        status_counts[status] += 1
        cost_unknown += int(status == "cost_unknown")
        comparator = result.get("comparator", {})
        comparator_timed_out = bool(isinstance(comparator, dict) and comparator.get("timed_out"))
        agent_error = result.get("agent_error", {})
        agent_timed_out = bool(
            isinstance(agent_error, dict) and agent_error.get("type") == "TimeoutError"
        )
        comparator_timeouts += int(comparator_timed_out)
        agent_timeouts += int(agent_timed_out)
        if "timeout" in status or comparator_timed_out or agent_timed_out:
            timeouts += 1
        calls_list = transcript.get("calls", [])
        if not isinstance(calls_list, list):
            raise ValueError(f"{problem_id}: transcript calls is not a list")
        calls += len(calls_list)
        phases = [_request_phase(call) for call in calls_list]
        problem_planning_calls = phases.count("planning")
        problem_restarts = phases.count("restart")
        problem_responses = sum(bool(_response_content(call)) for call in calls_list)
        problem_memos_returned = sum(
            phase == "planning" and bool(_response_content(call))
            for phase, call in zip(phases, calls_list)
        )
        problem_memos_injected = sum(
            phase == "planning"
            and index + 1 < len(calls_list)
            and "Strategy memo to follow:"
            in json.dumps(calls_list[index + 1].get("request", {}))
            for index, phase in enumerate(phases)
        )
        planning_calls += problem_planning_calls
        restarts += problem_restarts
        responses += problem_responses
        planning_memos_returned += problem_memos_returned
        planning_memos_injected += problem_memos_injected
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
            attempts = metadata.get("attempts", [])
            if isinstance(attempts, list):
                for attempt in attempts:
                    reason = attempt.get("restart_reason") if isinstance(attempt, dict) else None
                    if reason:
                        restart_reasons[str(reason)] = restart_reasons.get(str(reason), 0) + 1
        problem_summaries[problem_id] = {
            "status": status,
            "passed": bool(result.get("passed")),
            "calls": len(calls_list),
            "responses_with_content": problem_responses,
            "planning_calls": problem_planning_calls,
            "planning_memos_returned": problem_memos_returned,
            "planning_memos_injected": problem_memos_injected,
            "restart_calls": problem_restarts,
            "agent_timeout": agent_timed_out,
            "comparator_timeout": comparator_timed_out,
            "wall_s": round(float(result.get("wall_s", 0.0)), 3),
            "cost_usd": round(
                float(budget.get("spent_usd", 0.0)) if isinstance(budget, dict) else 0.0,
                10,
            ),
        }
    return {
        "condition": condition_id,
        "model": model,
        "policy": policy,
        "commit": provenance.get("git_commit"),
        "score": len(passed),
        "passed_problems": passed,
        "calls": calls,
        "candidate_generation_calls": calls - planning_calls,
        "responses_with_content": responses,
        "prompt_tokens": prompt_tokens,
        "completion_tokens": completion_tokens,
        "total_tokens": total_tokens,
        "cost_usd": round(cost, 10),
        "wall_s": round(wall_s, 3),
        "timeouts": timeouts,
        "agent_timeouts": agent_timeouts,
        "comparator_timeouts": comparator_timeouts,
        "cost_unknown": cost_unknown,
        "status_counts": dict(sorted(status_counts.items())),
        "restarts": restarts,
        "planning_calls": planning_calls,
        "planning_memos_returned": planning_memos_returned,
        "planning_memos_injected": planning_memos_injected,
        "restart_reasons": restart_reasons,
        "restart_reasons_observed": sum(restart_reasons.values()),
        "restart_reasons_unobserved": max(0, restarts - sum(restart_reasons.values())),
        "problems": problem_summaries,
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
            "candidate_generation_calls": qwen["candidate_generation_calls"] + gpt["candidate_generation_calls"],
            "responses_with_content": qwen["responses_with_content"] + gpt["responses_with_content"],
            "prompt_tokens": qwen["prompt_tokens"] + gpt["prompt_tokens"],
            "completion_tokens": qwen["completion_tokens"] + gpt["completion_tokens"],
            "total_tokens": qwen["total_tokens"] + gpt["total_tokens"],
            "cost_usd": round(qwen["cost_usd"] + gpt["cost_usd"], 10),
            "wall_s": round(qwen["wall_s"] + gpt["wall_s"], 3),
            "timeouts": qwen["timeouts"] + gpt["timeouts"],
            "agent_timeouts": qwen["agent_timeouts"] + gpt["agent_timeouts"],
            "comparator_timeouts": qwen["comparator_timeouts"] + gpt["comparator_timeouts"],
            "cost_unknown": qwen["cost_unknown"] + gpt["cost_unknown"],
            "restarts": qwen["restarts"] + gpt["restarts"],
            "planning_calls": qwen["planning_calls"] + gpt["planning_calls"],
            "planning_memos_returned": qwen["planning_memos_returned"] + gpt["planning_memos_returned"],
            "planning_memos_injected": qwen["planning_memos_injected"] + gpt["planning_memos_injected"],
        }
    return {"schema_version": 2, "conditions": conditions, "policies": policies}


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
