#!/usr/bin/env python3
"""Launch one frozen, manifest-driven solo uplift condition."""

from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
import socket
import subprocess
import sys
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
for import_root in (ROOT / "src", ROOT):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from uplift_pilot.constants import DESIGN_ID
from uplift_pilot.experiment import (
    EXPECTED_CONDITIONS,
    EXPERIMENT_RELATIVE,
    Condition,
    load_condition,
    load_problem_ids,
    sha256_file,
)


DEFAULT_WORKTREES = Path("/opt/experiments")
DEFAULT_RESULTS = Path("/opt/takehome-results")


def _run(command: list[str], *, cwd: Path | None = None, capture: bool = True) -> str:
    result = subprocess.run(
        command,
        cwd=cwd or ROOT,
        check=True,
        text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.PIPE if capture else None,
    )
    return result.stdout.strip() if capture else ""


def _require_clean_source() -> str:
    top = Path(_run(["git", "rev-parse", "--show-toplevel"])).resolve()
    if top != ROOT:
        raise RuntimeError(f"launcher root {ROOT} is not Git top-level {top}")
    status = _run(["git", "status", "--porcelain", "--untracked-files=all"])
    if status:
        raise RuntimeError(f"source tree is dirty; commit or remove these paths first:\n{status}")
    return _run(["git", "rev-parse", "HEAD"])


def _validate_env(path: Path) -> None:
    if not path.is_file():
        raise RuntimeError(f"missing runtime environment: {path}")
    configured = False
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if stripped.startswith("OPENROUTER_API_KEY=") and stripped.partition("=")[2].strip():
            configured = True
            break
    if not configured:
        raise RuntimeError("OPENROUTER_API_KEY is empty or absent in .env")


def _validate_contract(condition_path: Path) -> tuple[Condition, Path, tuple[str, ...]]:
    experiment = ROOT / EXPERIMENT_RELATIVE
    expected_parent = (experiment / "conditions").resolve()
    if condition_path.resolve().parent != expected_parent:
        raise RuntimeError(f"condition must be one of the checked-in files under {expected_parent}")
    for condition_id in EXPECTED_CONDITIONS:
        load_condition(expected_parent / f"{condition_id}.json")
    condition = load_condition(condition_path)
    problems_path = experiment / "problems.txt"
    problems = load_problem_ids(problems_path)
    if DESIGN_ID != "uplift-pilot-v1":
        raise RuntimeError(f"unexpected imported design id: {DESIGN_ID}")
    return condition, problems_path, problems


def _materialize_problem_set(worktree: Path, problem_ids: tuple[str, ...]) -> Path:
    source = worktree / "sample-problems"
    destination = worktree / ".uplift-runtime" / "problem-set"
    destination.mkdir(parents=True)
    manifest = json.loads((source / "manifest.json").read_text(encoding="utf-8"))
    entries = {entry["id"]: entry for entry in manifest["problems"]}
    selected = []
    for problem_id in problem_ids:
        if problem_id not in entries:
            raise RuntimeError(f"problem missing from sample manifest: {problem_id}")
        shutil.copytree(source / problem_id, destination / problem_id)
        selected.append(entries[problem_id])
    (destination / "manifest.json").write_text(
        json.dumps({"schema_version": 1, "set": "uplift-pilot-v1", "problems": selected}, indent=2) + "\n",
        encoding="utf-8",
    )
    return destination


def _host_metadata() -> dict[str, Any]:
    memory_kib = None
    try:
        for line in Path("/proc/meminfo").read_text(encoding="utf-8").splitlines():
            if line.startswith("MemTotal:"):
                memory_kib = int(line.split()[1])
                break
    except OSError:
        pass
    return {
        "hostname": socket.gethostname(),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "cpu_count": os.cpu_count(),
        "memory_total_kib": memory_kib,
    }


def _write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _ensure_targets_unused(worktree: Path, run_root: Path) -> None:
    if worktree.exists():
        raise FileExistsError(f"worktree already exists: {worktree}")
    if run_root.exists():
        raise FileExistsError(f"run directory already exists: {run_root}")


def _process_environment(effective: dict[str, Any], base: dict[str, str]) -> dict[str, str]:
    environment = dict(base)
    environment.update(effective["environment"])
    return environment


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("condition", type=Path)
    parser.add_argument("--check", action="store_true", help="validate without creating files or launching")
    parser.add_argument("--worktrees-root", type=Path, default=Path(os.environ.get("EXPERIMENTS_ROOT", DEFAULT_WORKTREES)))
    parser.add_argument("--results-root", type=Path, default=Path(os.environ.get("RESULTS_ROOT", DEFAULT_RESULTS)))
    args = parser.parse_args(argv)

    try:
        for executable in ("git", "bash"):
            if shutil.which(executable) is None:
                raise RuntimeError(f"required executable is unavailable: {executable}")
        commit = _require_clean_source()
        condition, problems_path, problem_ids = _validate_contract(args.condition)
        source_env = ROOT / ".env"
        _validate_env(source_env)
    except (RuntimeError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"launcher refusal: {exc}", file=sys.stderr)
        return 1

    if args.check:
        check_effective = condition.effective_configuration(
            problems_path=ROOT / ".uplift-runtime" / "problem-set",
            output_root=Path("/non-mutating-check/outputs"),
        )
        print(f"launcher check passed: condition={condition.condition}")
        print(f"commit={commit}")
        print(f"design={DESIGN_ID}")
        print(f"model={condition.model}")
        print(f"policy={condition.policy}")
        print(f"lean_image={check_effective['environment']['LEAN_IMAGE']}")
        return 0

    launched_at = datetime.now(UTC).strftime("%Y%m%dT%H%M%S.%fZ")
    name = f"{condition.condition}-{launched_at}-{commit[:8]}"
    worktree = args.worktrees_root.resolve() / name
    run_root = args.results_root.resolve() / name
    try:
        _ensure_targets_unused(worktree, run_root)
    except FileExistsError as exc:
        print(f"launcher refusal: {exc}", file=sys.stderr)
        return 1

    try:
        args.worktrees_root.mkdir(parents=True, exist_ok=True)
        args.results_root.mkdir(parents=True, exist_ok=True)
        run_root.mkdir()
        (run_root / "outputs").mkdir()
        shutil.copyfile(condition.path, run_root / "condition.json")
        _run(["git", "worktree", "add", "--detach", str(worktree), commit], capture=False)
        shutil.copy2(source_env, worktree / ".env")
        os.chmod(worktree / ".env", 0o600)
        frozen_problems = _materialize_problem_set(worktree, problem_ids)
        frozen_condition = load_condition(
            worktree / EXPERIMENT_RELATIVE / "conditions" / condition.path.name
        )
        if (frozen_condition.model, frozen_condition.policy) != (condition.model, condition.policy):
            raise RuntimeError("frozen condition does not match validated source condition")
        setup_env = os.environ.copy()
        setup_env["LEAN_IMAGE"] = str(condition.resources["lean_image"])
        subprocess.run(["bash", "scripts/setup.sh"], cwd=worktree, env=setup_env, check=True)
        python = worktree / ".venv" / "bin" / "python"
        if not python.is_file():
            raise RuntimeError(f"setup did not create {python}")
        output_root = run_root / "outputs"
        effective = condition.effective_configuration(
            problems_path=frozen_problems, output_root=output_root
        )
        command = [
            str(python),
            str(worktree / "run.py"),
            "--problems",
            effective["problems"],
            "--out",
            effective["output_root"],
            "--n-workers",
            str(effective["n_workers"]),
            "--agent",
            effective["agent"],
        ]
        provenance = {
            "schema_version": 1,
            "experiment": "uplift-pilot-v1",
            "design_id": DESIGN_ID,
            "condition": condition.condition,
            "model": condition.model,
            "policy": condition.policy,
            "launched_at": launched_at,
            "git_commit": commit,
            "manifest_sha256": condition.manifest_sha256,
            "problem_list_sha256": sha256_file(problems_path),
            "launcher_sha256": sha256_file(ROOT / "scripts" / "launch_uplift_pilot.py"),
            "lean_image": condition.resources["lean_image"],
            "worktree": str(worktree),
            "run_root": str(run_root),
            "command": command,
            "effective_configuration": effective,
            "host": _host_metadata(),
        }
        _write_json(run_root / "provenance.json", provenance)
        log_path = run_root / "run.log"
        process_env = _process_environment(effective, dict(os.environ))
        with log_path.open("ab", buffering=0) as log:
            process = subprocess.Popen(
                command,
                cwd=worktree,
                env=process_env,
                stdin=subprocess.DEVNULL,
                stdout=log,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
        (run_root / "run.pid").write_text(f"{process.pid}\n", encoding="utf-8")
    except BaseException as exc:
        print(f"launch failed; preserved partial artifact at {run_root}: {type(exc).__name__}: {exc}", file=sys.stderr)
        return 1

    print("uplift pilot condition launched")
    print(f"pid={process.pid}")
    print(f"commit={commit}")
    print(f"worktree={worktree}")
    print(f"run_root={run_root}")
    print(f"log={log_path}")
    print(f"provenance={run_root / 'provenance.json'}")
    print(f"monitor_pid=ps -p {process.pid} -o pid,etime,stat,cmd")
    print(f"monitor_log=tail -f {log_path}")
    print(f"monitor_results=find {output_root} -name result.json -print")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
