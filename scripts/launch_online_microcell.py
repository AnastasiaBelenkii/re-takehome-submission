#!/usr/bin/env python3
"""Launch one bounded online-development microcell with durable artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


STRATEGIES = {
    "c0": "none",
    "c1": "reciprocal-once-v1",
    "c2": "reciprocal-every-eligible-v1",
    "c0plus": "none",
    "c1plus": "progress-event-latest-v1",
    "c0plus-reserve": "none",
    "c1plus-fill-reserve": "progress-fill-event-latest-v2",
    "qwen-solo-plus": "none",
    "gptoss-solo-plus": "none",
}
SALVAGE_CONDITIONS = frozenset({
    "c0plus", "c1plus", "c0plus-reserve", "c1plus-fill-reserve",
    "qwen-solo-plus", "gptoss-solo-plus",
})
AGENT_REFERENCES = {
    "qwen-solo-plus": "submission.candidates:create_qwen_solo_plus_agent",
    "gptoss-solo-plus": "submission.candidates:create_gptoss_solo_plus_agent",
}
LEAN_IMAGE = (
    "ghcr.io/verifiedmechanisms/re-takehome-lean"
    "@sha256:ee48287cd31c0a7df572093a879ed7289c2f01fec6c7af8716c605fc8c670c39"
)


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def result_summary(output: Path, task_root: Path) -> dict[str, object]:
    results = sorted(output.rglob("result.json"))
    if len(results) != 1:
        return {"result_artifact_count": len(results), "result_status": "missing_or_ambiguous"}
    path = results[0]
    try:
        result = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return {"result_artifact_count": 1, "result_status": f"invalid: {type(exc).__name__}"}
    return {
        "result_artifact_count": 1,
        "result_path": str(path.relative_to(task_root)),
        "result_status": result.get("status"),
        "result_passed": bool(result.get("passed")),
        "result_calls_dispatched": (result.get("agent_metadata") or {}).get("calls_dispatched"),
    }


def preliminary_summary(output: Path, task_root: Path) -> dict[str, object] | None:
    """Summarize the final agent checkpoint while exact judging continues."""
    checkpoints = sorted(output.rglob("checkpoint.json"))
    if len(checkpoints) != 1:
        return None
    path = checkpoints[0]
    try:
        payload = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError):
        return None
    metadata = payload.get("metadata") or {}
    # The agent may save provisional recovery checkpoints during its run. The
    # complete scheduler metadata is written only after Agent.solve returns.
    if metadata.get("scheduler") != "independent-track-v1":
        return None
    attempts = [
        attempt
        for track in (metadata.get("tracks") or {}).values()
        for attempt in track.get("attempts", [])
    ]
    deterministic = metadata.get("deterministic") or {}
    packet_events = metadata.get("packet_events") or []
    return {
        "schema_version": 1,
        "status": "preliminary_agent_complete",
        "final_judging_pending": True,
        "checkpoint_path": str(path.relative_to(task_root)),
        "scheduler": metadata.get("scheduler"),
        "calls_attempted": metadata.get("calls_attempted"),
        "calls_dispatched": metadata.get("calls_dispatched"),
        "physical_requests": metadata.get("physical_requests"),
        "dispatch_cutoff_reached": bool(metadata.get("dispatch_cutoff_reached")),
        "structural_rejections": sum(
            not bool(attempt.get("required_declarations_present")) for attempt in attempts
        ),
        "warm_lean_successes": (
            sum(bool(attempt.get("lean_accepted")) for attempt in attempts)
            + int(bool(deterministic.get("lean_accepted")))
        ),
        "fresh_verified_successes": (
            sum(bool(attempt.get("accepted")) for attempt in attempts)
            + int(bool(deterministic.get("accepted")))
        ),
        "packets_generated": len(packet_events),
        "packets_used": sum("used_on_call" in event for event in packet_events),
        "packets_pending": sum(
            int(track.get("pending_peer_packets") or 0)
            for track in (metadata.get("tracks") or {}).values()
        ),
    }


def validate_api_key(worktree: Path) -> None:
    env_path = worktree / ".env"
    try:
        lines = env_path.read_text().splitlines()
    except OSError as exc:
        raise RuntimeError("frozen checkout has no readable .env") from exc
    configured = any(
        line.strip().startswith("OPENROUTER_API_KEY=")
        and line.partition("=")[2].strip()
        for line in lines
    )
    if not configured:
        raise RuntimeError("frozen checkout has no configured OPENROUTER_API_KEY")


def execute(worktree: Path, descriptor_path: Path, task_root: Path) -> int:
    validate_api_key(worktree)
    descriptor = json.loads(descriptor_path.read_text())
    task = descriptor["task"]
    condition = task["condition"]
    if condition not in STRATEGIES or task["strategy"] != STRATEGIES[condition]:
        raise ValueError("condition/strategy pair is not an unchanged v2 arm")
    problem = task["problem"]
    source = worktree / "sample-problems" / problem
    sample_manifest = worktree / "sample-problems" / "manifest.json"
    manifest = json.loads(sample_manifest.read_text())
    entry = next(item for item in manifest["problems"] if item["id"] == problem)
    problem_set = task_root / "problem-set"
    (problem_set / problem).mkdir(parents=True, exist_ok=False)
    shutil.copy2(source / "challenge.lean", problem_set / problem / "challenge.lean")
    shutil.copy2(source / "problem.md", problem_set / problem / "problem.md")
    atomic(problem_set / "manifest.json", {
        "schema_version": 1,
        "set": task["task_id"],
        "problems": [entry],
    })

    resources = descriptor["resources"]
    output = task_root / "outputs"
    agent_reference = AGENT_REFERENCES.get(
        condition, "collaboration_engine_v2.agent:create_agent"
    )
    argv = [
        str(worktree / ".venv/bin/python"), str(worktree / "run.py"),
        "--problems", str(problem_set), "--out", str(output),
        "--n-workers", "1", "--agent", agent_reference,
    ]
    atomic(task_root / "provenance.json", {
        "schema_version": 1,
        "experiment": descriptor.get("experiment", "online-development-v1-stage2"),
        "design_id": "collaboration-engine-v2",
        "task": task,
        "git_commit": descriptor["git_commit"],
        "dispatched_at": descriptor["dispatched_at"],
        "worker": descriptor["worker"],
        "resources": resources,
        "sample_manifest_sha256": sha256(sample_manifest),
        "agent_sha256": sha256(worktree / "collaboration_engine_v2" / "agent.py"),
        "strategies_sha256": sha256(worktree / "collaboration_engine_v2" / "strategies.py"),
        "salvage_sha256": sha256(worktree / "collaboration_engine_v2" / "salvage.py"),
        "lean_image": LEAN_IMAGE,
        "command": argv,
    })
    environment = dict(os.environ)
    environment.update({
        # Shared remote virtual environments may contain editable-install
        # pointers to an older checkout. The frozen task worktree must win.
        "PYTHONPATH": os.pathsep.join([str(worktree / "src"), str(worktree)]),
        "LEAN_IMAGE": LEAN_IMAGE,
        "VM_TIME_LIMIT_S": str(resources["outer_time_s"]),
        "VM_VERIFY_RESERVE_S": str(resources["verify_reserve_s"]),
        "VM_BUDGET_USD": str(resources["budget_usd"]),
        "LEAN_CHECK_TIMEOUT_S": str(resources["lean_check_timeout_s"]),
        "COMPARATOR_TIMEOUT_S": str(resources["comparator_timeout_s"]),
        "COLLAB_DESIGN_ID": "collaboration-engine-v2",
        "COLLAB_CONDITION": condition,
        "COLLAB_STRATEGY": task["strategy"],
        "COLLAB_SEED": str(task["seed"]),
        "COLLAB_MAX_CALLS_PER_MODEL": str(resources["max_calls_per_model"]),
        "COLLAB_GENERATION_MAX_TOKENS": str(resources["generation_max_tokens"]),
        "COLLAB_TEMPERATURE": str(resources["temperature"]),
        "COLLAB_MAX_RESTARTS": str(resources["max_restarts"]),
        "COLLAB_DIAGNOSTIC_CHARS": str(resources["diagnostic_chars"]),
        "COLLAB_FAILURE_MEMORY_CHARS": str(resources["failure_memory_chars"]),
        "COLLAB_PEER_PACKET_CHARS": str(resources["peer_packet_chars"]),
        "COLLAB_DISPATCH_CUTOFF_S": str(resources["dispatch_cutoff_s"]),
        "COLLAB_MAX_FREE_429_RETRIES": str(resources["max_cost_free_429_retries"]),
        "COLLAB_ENABLE_SALVAGE": "1" if condition in SALVAGE_CONDITIONS else "0",
        "COLLAB_SALVAGE_CHECK_TIMEOUT_S": str(resources.get("salvage_check_timeout_s", 2)),
        "COLLAB_MODEL_CALL_WALL_TIMEOUT_S": str(
            resources.get("model_call_wall_timeout_s", 420)
        ),
        "COLLAB_FAST_TRACK_RESERVED_CALLS": str(
            resources.get("fast_track_reserved_calls", 0)
        ),
        "COLLAB_RESERVE_RELEASE_MARGIN_S": str(
            resources.get("reserve_release_margin_s", 120)
        ),
    })
    with (task_root / "run.log").open("ab", buffering=0) as log:
        process = subprocess.Popen(
            argv, cwd=worktree, env=environment,
            stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
        )
        preliminary_written = False
        while process.poll() is None:
            if not preliminary_written:
                preliminary = preliminary_summary(output, task_root)
                if preliminary is not None:
                    preliminary["observed_at"] = now()
                    atomic(task_root / "preliminary-status.json", preliminary)
                    preliminary_written = True
            time.sleep(0.25)
        if not preliminary_written:
            preliminary = preliminary_summary(output, task_root)
            if preliminary is not None:
                preliminary["observed_at"] = now()
                atomic(task_root / "preliminary-status.json", preliminary)
    status = {
        "schema_version": 1,
        "task_id": task["task_id"],
        "exit_code": process.returncode,
        "finished_at": now(),
        **result_summary(output, task_root),
    }
    atomic(task_root / "microcell-status.json", status)
    return process.returncode


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--worktree", type=Path, required=True)
    parser.add_argument("--descriptor", type=Path, required=True)
    parser.add_argument("--task-root", type=Path, required=True)
    parser.add_argument("--execute", action="store_true")
    args = parser.parse_args()
    worktree = args.worktree.resolve()
    descriptor = args.descriptor.resolve()
    task_root = args.task_root.resolve()
    if args.execute:
        try:
            return execute(worktree, descriptor, task_root)
        except BaseException as exc:
            atomic(task_root / "microcell-status.json", {
                "schema_version": 1,
                "task_id": task_root.name,
                "exit_code": 255,
                "finished_at": now(),
                "error": f"{type(exc).__name__}: {exc}",
            })
            return 255
    if task_root.exists():
        raise SystemExit("task root already exists")
    task_root.parent.mkdir(parents=True, exist_ok=True)
    task_root.mkdir()
    command = [
        str(worktree / ".venv/bin/python"), str(Path(__file__).resolve()),
        "--worktree", str(worktree), "--descriptor", str(descriptor),
        "--task-root", str(task_root), "--execute",
    ]
    with (task_root / "launcher.log").open("ab", buffering=0) as log:
        process = subprocess.Popen(
            command, cwd=worktree, stdin=subprocess.DEVNULL,
            stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
        )
    atomic(task_root / "microcell-launch.json", {
        "schema_version": 1,
        "pid": process.pid,
        "launched_at": now(),
        "command": command,
    })
    print(json.dumps({"pid": process.pid, "task_root": str(task_root)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
