#!/usr/bin/env python3
"""Launch one frozen full-sample collaboration condition with provenance."""

from __future__ import annotations

import argparse
import hashlib
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
sys.path[:0] = [str(ROOT / "src"), str(ROOT)]

from collaboration_engine.constants import DESIGN_ID
from collaboration_engine.experiment import EXPERIMENT_RELATIVE, load_condition


def run(command: list[str], *, cwd: Path = ROOT, capture: bool = True) -> str:
    result = subprocess.run(
        command, cwd=cwd, check=True, text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.PIPE if capture else None,
    )
    return result.stdout.strip() if capture else ""


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def validate_env(path: Path) -> None:
    lines = path.read_text(encoding="utf-8").splitlines() if path.is_file() else []
    if not any(line.strip().startswith("OPENROUTER_API_KEY=") and line.partition("=")[2].strip() for line in lines):
        raise RuntimeError(f"{path} has no non-empty OPENROUTER_API_KEY")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("condition", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--worktrees-root", type=Path, default=Path("/opt/experiments"))
    parser.add_argument("--results-root", type=Path, default=Path("/opt/takehome-results"))
    args = parser.parse_args()
    try:
        if Path(run(["git", "rev-parse", "--show-toplevel"])).resolve() != ROOT:
            raise RuntimeError("launcher is not running from its Git root")
        dirty = run(["git", "status", "--porcelain", "--untracked-files=all"])
        if dirty:
            raise RuntimeError(f"source tree is dirty:\n{dirty}")
        commit = run(["git", "rev-parse", "HEAD"])
        condition_path = args.condition.resolve()
        expected_parent = (ROOT / EXPERIMENT_RELATIVE / "conditions").resolve()
        if condition_path.parent != expected_parent:
            raise RuntimeError(f"condition must be checked in under {expected_parent}")
        condition = load_condition(condition_path)
        # Load both arms so a malformed comparator blocks either launch.
        for path in sorted(expected_parent.glob("*.json")):
            load_condition(path)
        validate_env(ROOT / ".env")
        manifest = ROOT / "sample-problems" / "manifest.json"
        if len(json.loads(manifest.read_text(encoding="utf-8"))["problems"]) != 16:
            raise RuntimeError("sample problem manifest does not contain exactly 16 problems")
    except Exception as exc:
        print(f"launcher refusal: {exc}", file=sys.stderr)
        return 1

    if args.check:
        print(f"launcher check passed: {condition.condition} at {commit}")
        return 0

    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    name = f"{condition.condition}-{stamp}-{commit[:8]}"
    worktree = args.worktrees_root.resolve() / name
    run_root = args.results_root.resolve() / name
    if worktree.exists() or run_root.exists():
        print("launcher refusal: generated target already exists", file=sys.stderr)
        return 1
    try:
        worktree.parent.mkdir(parents=True, exist_ok=True)
        run_root.mkdir(parents=True)
        (run_root / "outputs").mkdir()
        shutil.copy2(condition.path, run_root / "condition.json")
        run(["git", "worktree", "add", "--detach", str(worktree), commit], capture=False)
        shutil.copy2(ROOT / ".env", worktree / ".env")
        os.chmod(worktree / ".env", 0o600)
        setup_env = dict(os.environ, LEAN_IMAGE=condition.resources["lean_image"])
        subprocess.run(["bash", "scripts/setup.sh"], cwd=worktree, env=setup_env, check=True)
        effective = condition.effective_configuration(
            problems_path=worktree / "sample-problems",
            output_root=run_root / "outputs",
        )
        command = [
            str(worktree / ".venv/bin/python"), str(worktree / "run.py"),
            "--problems", effective["problems"], "--out", effective["output_root"],
            "--n-workers", str(effective["n_workers"]), "--agent", effective["agent"],
        ]
        provenance = {
            "schema_version": 1, "experiment": DESIGN_ID,
            "condition": condition.condition, "collaboration_strategy": condition.strategy,
            "git_commit": commit, "launched_at": stamp,
            "manifest_sha256": sha256(condition.path),
            "sample_manifest_sha256": sha256(manifest),
            "launcher_sha256": sha256(ROOT / "scripts/launch_collaboration_condition.py"),
            "worktree": str(worktree), "run_root": str(run_root), "command": command,
            "effective_configuration": effective,
            "host": {"hostname": socket.gethostname(), "platform": platform.platform(), "python": platform.python_version(), "cpu_count": os.cpu_count()},
        }
        (run_root / "provenance.json").write_text(json.dumps(provenance, indent=2, sort_keys=True) + "\n")
        process_env = dict(os.environ)
        process_env.update(effective["environment"])
        with (run_root / "run.log").open("ab", buffering=0) as log:
            process = subprocess.Popen(
                command, cwd=worktree, env=process_env, stdin=subprocess.DEVNULL,
                stdout=log, stderr=subprocess.STDOUT, start_new_session=True,
            )
        (run_root / "run.pid").write_text(f"{process.pid}\n")
    except BaseException as exc:
        print(f"launch failed; partial artifacts preserved at {run_root}: {exc}", file=sys.stderr)
        return 1
    print("collaboration condition launched")
    print(f"pid={process.pid}")
    print(f"run_root={run_root}")
    print(f"log={run_root / 'run.log'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
