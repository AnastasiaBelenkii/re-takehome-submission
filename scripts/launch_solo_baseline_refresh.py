#!/usr/bin/env python3
"""Validate and launch the frozen two-condition solo baseline refresh."""

from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
import socket
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
for import_root in (ROOT / "src", ROOT):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from baseline_refresh.experiment import (
    AGENT_SHA256,
    EXPECTED_CONDITIONS,
    EXPERIMENT_ID,
    EXPERIMENT_RELATIVE,
    PROBLEM_MANIFEST_SHA256,
    UPSTREAM_FIX_COMMIT,
    load_condition,
    sha256_file,
)

DEFAULT_WORKTREES = Path("/opt/experiments")
DEFAULT_RESULTS = Path("/opt/takehome-results")


def _run(command: list[str], *, cwd: Path = ROOT) -> str:
    result = subprocess.run(command, cwd=cwd, check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return result.stdout.strip()


def _write(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _validate_env(path: Path) -> None:
    if not path.is_file() or not any(
        line.strip().startswith("OPENROUTER_API_KEY=") and line.partition("=")[2].strip()
        for line in path.read_text(encoding="utf-8").splitlines()
    ):
        raise RuntimeError("OPENROUTER_API_KEY is empty or absent in .env")


def _host() -> dict[str, object]:
    memory_kib = None
    try:
        memory_kib = next(
            int(line.split()[1])
            for line in Path("/proc/meminfo").read_text(encoding="utf-8").splitlines()
            if line.startswith("MemTotal:")
        )
    except (OSError, StopIteration, ValueError):
        pass
    return {
        "hostname": socket.gethostname(),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "cpu_count": os.cpu_count(),
        "memory_total_kib": memory_kib,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--worktrees-root", type=Path, default=DEFAULT_WORKTREES)
    parser.add_argument("--results-root", type=Path, default=DEFAULT_RESULTS)
    parser.add_argument("--confirm-paid-launch")
    args = parser.parse_args(argv)
    try:
        if _run(["git", "rev-parse", "--show-toplevel"]) != str(ROOT):
            raise RuntimeError("launcher is not running from the repository root")
        status = _run(["git", "status", "--porcelain", "--untracked-files=all"])
        if status:
            raise RuntimeError(f"source tree is dirty:\n{status}")
        commit = _run(["git", "rev-parse", "HEAD"])
        subprocess.run(["git", "merge-base", "--is-ancestor", UPSTREAM_FIX_COMMIT, commit], cwd=ROOT, check=True)
        source_env = ROOT / ".env"
        _validate_env(source_env)
        manifests = {}
        for condition_id in EXPECTED_CONDITIONS:
            path = ROOT / EXPERIMENT_RELATIVE / "conditions" / f"{condition_id}.json"
            manifests[condition_id] = load_condition(path)
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"launcher refusal: {exc}", file=sys.stderr)
        return 1

    print(f"check passed: experiment={EXPERIMENT_ID}")
    print(f"commit={commit}")
    print(f"upstream_fix_commit={UPSTREAM_FIX_COMMIT}")
    print(f"agent_sha256={AGENT_SHA256}")
    print(f"problem_manifest_sha256={PROBLEM_MANIFEST_SHA256}")
    print("order=qwen-solo,gpt-solo; n_workers=2 each; execution=sequential")
    if args.check:
        return 0
    if args.confirm_paid_launch != "I_UNDERSTAND_THIS_LAUNCHES_PAID_RUNS":
        print("launcher refusal: paid-launch confirmation is missing", file=sys.stderr)
        return 2

    launched_at = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    name = f"{EXPERIMENT_ID}-{launched_at}-{commit[:8]}"
    worktree = args.worktrees_root.resolve() / name
    run_root = args.results_root.resolve() / name
    if worktree.exists() or run_root.exists():
        print("launcher refusal: worktree or run root already exists", file=sys.stderr)
        return 1
    try:
        args.worktrees_root.mkdir(parents=True, exist_ok=True)
        args.results_root.mkdir(parents=True, exist_ok=True)
        run_root.mkdir()
        subprocess.run(["git", "worktree", "add", "--detach", str(worktree), commit], cwd=ROOT, check=True)
        shutil.copy2(source_env, worktree / ".env")
        os.chmod(worktree / ".env", 0o600)
        setup_environment = dict(os.environ)
        setup_environment["LEAN_IMAGE"] = str(next(iter(manifests.values())).resources["lean_image"])
        subprocess.run(["bash", "scripts/setup.sh"], cwd=worktree, env=setup_environment, check=True)
        state = {
            "schema_version": 1,
            "experiment": EXPERIMENT_ID,
            "state": "launched",
            "launched_at": launched_at,
            "finished_at": None,
            "git_commit": commit,
            "upstream_fix_commit": UPSTREAM_FIX_COMMIT,
            "agent_sha256": AGENT_SHA256,
            "problem_manifest_sha256": PROBLEM_MANIFEST_SHA256,
            "launcher_sha256": sha256_file(ROOT / "scripts" / "launch_solo_baseline_refresh.py"),
            "executor_sha256": sha256_file(ROOT / "scripts" / "execute_solo_baseline_refresh.py"),
            "host": _host(),
            "worktree": str(worktree),
            "run_root": str(run_root),
            "conditions": {
                condition_id: {
                    "state": "pending",
                    "model": condition.model,
                    "manifest_sha256": condition.manifest_sha256,
                    "effective_environment": condition.environment(),
                }
                for condition_id, condition in manifests.items()
            },
        }
        _write(run_root / "state.json", state)
        for condition_id, condition in manifests.items():
            condition_root = run_root / condition_id
            condition_root.mkdir()
            shutil.copy2(condition.path, condition_root / "condition.json")
        log_path = run_root / "run.log"
        command = [
            str(worktree / ".venv" / "bin" / "python"),
            str(worktree / "scripts" / "execute_solo_baseline_refresh.py"),
            "--run-root",
            str(run_root),
        ]
        with log_path.open("ab", buffering=0) as log:
            process = subprocess.Popen(
                command,
                cwd=worktree,
                env=dict(os.environ),
                stdin=subprocess.DEVNULL,
                stdout=log,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
        (run_root / "run.pid").write_text(f"{process.pid}\n", encoding="utf-8")
    except BaseException as exc:
        print(f"launch failed; partial artifacts preserved at {run_root}: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1

    print("solo baseline refresh launched")
    print(f"pid={process.pid}")
    print(f"commit={commit}")
    print(f"worktree={worktree}")
    print(f"run_root={run_root}")
    print(f"log={log_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
