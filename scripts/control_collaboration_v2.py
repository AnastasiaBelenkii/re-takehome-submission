#!/usr/bin/env python3
"""Resumable four-slot controller for the frozen collaboration-engine-v2 queue."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
from dataclasses import asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "src"), str(ROOT)]

from collaboration_engine_v2.constants import CONDITIONS, DESIGN_ID
from collaboration_engine_v2.experiment import (
    AGENT_REFERENCE, EXPERIMENT_RELATIVE, LEAN_IMAGE, Task, build_queue,
    effective_environment, load_condition, load_resources,
)

CONFIRMATION = "I_UNDERSTAND_THIS_LAUNCHES_PAID_C0_C1_C2_RUNS"


class ExistingProcess:
    """Poll a child launched by an earlier controller invocation."""
    def __init__(self, pid: int, task_root: Path) -> None:
        self.pid, self.task_root = pid, task_root

    def poll(self) -> int | None:
        if result_for(self.task_root) is not None:
            return 0
        try:
            os.kill(self.pid, 0)
            return None
        except ProcessLookupError:
            return 1
        except PermissionError:
            return None


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def atomic(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def command(argv: list[str], *, cwd: Path = ROOT, capture: bool = True) -> str:
    result = subprocess.run(argv, cwd=cwd, check=True, text=True,
                            stdout=subprocess.PIPE if capture else None,
                            stderr=subprocess.PIPE if capture else None)
    return result.stdout.strip() if capture else ""


def validate_source(commit: str, *, paid: bool) -> None:
    if command(["git", "rev-parse", "HEAD"]) != commit:
        raise ValueError("--commit is not the checked-out source commit")
    if command(["git", "status", "--porcelain", "--untracked-files=all"]):
        raise ValueError("source tree must be clean")
    if not __import__("re").fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("--commit must be a full Git SHA")
    if paid:
        lines = (ROOT / ".env").read_text(encoding="utf-8").splitlines()
        if not any(line.startswith("OPENROUTER_API_KEY=") and line.partition("=")[2].strip()
                   for line in lines):
            raise ValueError(".env has no OPENROUTER_API_KEY")


def prepare_slots(commit: str, roots: list[Path]) -> list[Path]:
    slots: list[Path] = []
    for index, parent in enumerate(roots):
        worktree = parent.resolve() / f"{DESIGN_ID}-{commit[:12]}-slot{index}"
        if not worktree.exists():
            worktree.parent.mkdir(parents=True, exist_ok=True)
            command(["git", "worktree", "add", "--detach", str(worktree), commit], capture=False)
            shutil.copy2(ROOT / ".env", worktree / ".env")
            os.chmod(worktree / ".env", 0o600)
            env = dict(os.environ, LEAN_IMAGE=LEAN_IMAGE)
            subprocess.run(["bash", "scripts/setup.sh"], cwd=worktree, env=env, check=True)
        if command(["git", "rev-parse", "HEAD"], cwd=worktree) != commit:
            raise ValueError(f"slot {index} is not frozen at {commit}")
        slots.append(worktree)
    return slots


def make_problem_set(worktree: Path, task_root: Path, task: Task) -> Path:
    problem = task.problem
    source = worktree / "sample-problems" / problem
    manifest = json.loads((worktree / "sample-problems/manifest.json").read_text())
    entry = next(item for item in manifest["problems"] if item["id"] == problem)
    target = task_root / "problem-set"
    (target / problem).mkdir(parents=True, exist_ok=False)
    shutil.copy2(source / "challenge.lean", target / problem / "challenge.lean")
    shutil.copy2(source / "problem.md", target / problem / "problem.md")
    atomic(target / "manifest.json", {"schema_version": 1, "set": task.task_id, "problems": [entry]})
    return target


def start_task(task: Task, slot: int, worktree: Path, results_root: Path,
               resources: dict[str, dict[str, Any]], commit: str) -> tuple[subprocess.Popen, Path]:
    task_root = results_root / "tasks" / task.task_id
    task_root.mkdir(parents=True, exist_ok=False)
    problem_set = make_problem_set(worktree, task_root, task)
    output = task_root / "outputs"
    profile = resources[task.profile]
    environment = effective_environment(task, profile, LEAN_IMAGE)
    argv = [str(worktree / ".venv/bin/python"), str(worktree / "run.py"),
            "--problems", str(problem_set), "--out", str(output), "--n-workers", "1",
            "--agent", AGENT_REFERENCE]
    provenance = {
        "schema_version": 1, "design_id": DESIGN_ID, "task": asdict(task),
        "git_commit": commit, "dispatched_at": now(), "slot": slot,
        "condition_manifest_sha256": sha256(worktree / EXPERIMENT_RELATIVE / "conditions" / f"{task.condition}.json"),
        "resources_manifest_sha256": sha256(worktree / EXPERIMENT_RELATIVE / "resources.json"),
        "sample_manifest_sha256": sha256(worktree / "sample-problems/manifest.json"),
        "effective_resources": profile, "lean_image": LEAN_IMAGE, "command": argv,
    }
    atomic(task_root / "provenance.json", provenance)
    process_env = dict(os.environ)
    process_env.update(environment)
    log = (task_root / "run.log").open("ab", buffering=0)
    process = subprocess.Popen(argv, cwd=worktree, env=process_env,
                               stdin=subprocess.DEVNULL, stdout=log,
                               stderr=subprocess.STDOUT, start_new_session=True)
    log.close()
    (task_root / "run.pid").write_text(f"{process.pid}\n", encoding="utf-8")
    return process, task_root


def result_for(task_root: Path) -> Path | None:
    matches = list((task_root / "outputs").rglob("result.json"))
    return matches[0] if len(matches) == 1 else None


def validate_group(results_root: Path, task_ids: list[str], label: str, worktree: Path) -> bool:
    report = results_root / "validation" / f"{label}.json"
    argv = [str(worktree / ".venv/bin/python"), str(worktree / "scripts/validate_collaboration_v2.py"),
            "--results-root", str(results_root), "--output", str(report)]
    for task_id in task_ids:
        argv.extend(["--task", task_id])
    return subprocess.run(argv, cwd=worktree).returncode == 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--results-root", type=Path, required=True)
    parser.add_argument("--slot-root", type=Path, action="append", default=[])
    parser.add_argument("--confirm-paid-launch")
    parser.add_argument("--sentinel-only", action="store_true")
    parser.add_argument("--check", action="store_true", help="validate the frozen source and queue without setup or spend")
    parser.add_argument("--poll-seconds", type=float, default=2.0)
    args = parser.parse_args()
    try:
        paid = not args.check and args.confirm_paid_launch == CONFIRMATION
        if not args.check and not paid:
            raise ValueError(f"paid launch requires --confirm-paid-launch {CONFIRMATION}")
        validate_source(args.commit, paid=paid)
        condition_dir = ROOT / EXPERIMENT_RELATIVE / "conditions"
        conditions = {name: load_condition(condition_dir / f"{name}.json") for name in CONDITIONS}
        resources = load_resources(ROOT / EXPERIMENT_RELATIVE / "resources.json")
        queue = build_queue(conditions)
        if args.check:
            counts = {stage: sum(item.stage == stage for item in queue)
                      for stage in ("sentinel", "core", "breadth", "deep")}
            print(json.dumps({"check": "passed", "commit": args.commit,
                              "tasks": len(queue), "stages": counts}, sort_keys=True))
            return 0
        roots = args.slot_root or [Path("/opt/experiments")] * 4
        if len(roots) != 4:
            raise ValueError("exactly four --slot-root values are required")
        worktrees = prepare_slots(args.commit, roots)
        state_path, results_root = args.state.resolve(), args.results_root.resolve()
        if state_path.exists():
            state = json.loads(state_path.read_text())
            if state.get("git_commit") != args.commit or state.get("queue") != [asdict(item) for item in queue]:
                raise ValueError("resume state does not match commit or frozen queue")
            if any(cell["status"] == "dispatching" for cell in state["tasks"].values()):
                raise ValueError("a dispatch has unknown completion; manual reconciliation required")
        else:
            state = {
                "schema_version": 1, "design_id": DESIGN_ID, "git_commit": args.commit,
                "created_at": now(), "updated_at": now(), "phase": "sentinel",
                "queue": [asdict(item) for item in queue],
                "tasks": {item.task_id: {"status": "pending"} for item in queue},
            }
            atomic(state_path, state)
        running: dict[int, tuple[Any, Task, Path]] = {}
        tasks_by_id = {item.task_id: item for item in queue}
        for task_id, cell in state["tasks"].items():
            if cell["status"] == "running":
                slot = int(cell["slot"])
                task_root = Path(cell["task_root"])
                running[slot] = (ExistingProcess(int(cell["pid"]), task_root),
                                 tasks_by_id[task_id], task_root)

        def eligible() -> list[Task]:
            pending = [item for item in queue if state["tasks"][item.task_id]["status"] == "pending"]
            phase = state["phase"]
            if phase == "sentinel": return [item for item in pending if item.stage == "sentinel"]
            if phase == "core": return [item for item in pending if item.stage == "core"]
            if phase == "stage2": return [item for item in pending if item.stage in {"breadth", "deep"}]
            return []

        while True:
            pending = eligible()
            for slot in range(4):
                if slot in running:
                    continue
                task = None
                if state["phase"] == "stage2":
                    wanted = "breadth" if slot == 3 else "deep"
                    task = next((item for item in pending if item.stage == wanted), None)
                    if wanted == "deep" and task is not None:
                        active_problem = next((active.problem for _p, active, _r in running.values()
                                               if active.stage == "deep"), task.problem)
                        task = next((item for item in pending
                                     if item.stage == "deep" and item.problem == active_problem), None)
                elif pending:
                    task = pending[0]
                if task is None:
                    continue
                # Persist intent before the first paid dispatch. A crash here is never auto-retried.
                state["tasks"][task.task_id] = {"status": "dispatching", "slot": slot, "at": now()}
                state["updated_at"] = now(); atomic(state_path, state)
                process, task_root = start_task(task, slot, worktrees[slot], results_root, resources, args.commit)
                state["tasks"][task.task_id].update({"status": "running", "pid": process.pid,
                                                     "task_root": str(task_root)})
                state["updated_at"] = now(); atomic(state_path, state)
                running[slot] = (process, task, task_root)
                pending.remove(task)

            for slot, (process, task, task_root) in list(running.items()):
                code = process.poll()
                if code is None: continue
                result = result_for(task_root)
                status = "complete" if code == 0 and result is not None else "exited_incomplete"
                state["tasks"][task.task_id].update({"status": status, "exit_code": code,
                                                     "finished_at": now(),
                                                     "result": str(result) if result else None})
                state["updated_at"] = now(); atomic(state_path, state)
                del running[slot]

            phase = state["phase"]
            phase_tasks = [item for item in queue if
                           (phase == "sentinel" and item.stage == "sentinel") or
                           (phase == "core" and item.stage == "core") or
                           (phase == "stage2" and item.stage in {"breadth", "deep"})]
            if not running and phase_tasks and all(state["tasks"][item.task_id]["status"] != "pending"
                                                   for item in phase_tasks):
                if any(state["tasks"][item.task_id]["status"] != "complete" for item in phase_tasks):
                    state["phase"] = "incomplete"; atomic(state_path, state); return 4
                if phase == "sentinel":
                    ok = validate_group(results_root, [item.task_id for item in phase_tasks], "sentinel", worktrees[0])
                    subprocess.run([str(worktrees[0] / ".venv/bin/python"),
                                    str(worktrees[0] / "scripts/analyze_collaboration_v2.py"),
                                    "--results-root", str(results_root)])
                    state["sentinel_integrity"] = "passed" if ok else "failed"
                    if not ok:
                        state["phase"] = "integrity_failed"; atomic(state_path, state); return 5
                    if args.sentinel_only:
                        state["phase"] = "sentinel_complete"; atomic(state_path, state); return 0
                    state["phase"] = "core"
                elif phase == "core":
                    core_ids = [item.task_id for item in queue if item.stage in {"sentinel", "core"}]
                    ok = validate_group(results_root, core_ids, "core", worktrees[0])
                    state["core_integrity"] = "passed" if ok else "failed"
                    if not ok:
                        state["phase"] = "integrity_failed"; atomic(state_path, state); return 5
                    state["phase"] = "stage2"
                else:
                    all_ids = [item.task_id for item in queue]
                    ok = validate_group(results_root, all_ids, "final", worktrees[0])
                    state["final_integrity"] = "passed" if ok else "failed"
                    state["phase"] = "complete" if ok else "integrity_failed"
                    state["updated_at"] = now(); atomic(state_path, state)
                    if ok:
                        subprocess.run([str(worktrees[0] / ".venv/bin/python"),
                                        str(worktrees[0] / "scripts/analyze_collaboration_v2.py"),
                                        "--results-root", str(results_root)])
                    return 0 if ok else 5
                state["updated_at"] = now(); atomic(state_path, state)
            time.sleep(max(0.1, args.poll_seconds))
    except (Exception, KeyboardInterrupt) as exc:
        print(f"controller refusal: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
