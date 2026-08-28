#!/usr/bin/env python3
"""Launch one frozen full-sample baseline/control replication."""

from __future__ import annotations

import argparse, json, os, platform, shutil, socket, subprocess, sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "src"), str(ROOT)]
from baseline_controls.experiment import EXPERIMENT_RELATIVE, RUNS, UPSTREAM_FIX_COMMIT, load_run, sha256_file


def command(argv: list[str], *, cwd: Path = ROOT, capture: bool = True) -> str:
    result = subprocess.run(argv, cwd=cwd, check=True, text=True,
                            stdout=subprocess.PIPE if capture else None,
                            stderr=subprocess.PIPE if capture else None)
    return result.stdout.strip() if capture else ""


def validate_env(path: Path) -> None:
    lines = path.read_text(encoding="utf-8").splitlines() if path.is_file() else []
    if not any(line.strip().startswith("OPENROUTER_API_KEY=") and line.partition("=")[2].strip() for line in lines):
        raise RuntimeError(".env has no non-empty OPENROUTER_API_KEY")


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--confirm-paid-launch")
    parser.add_argument("--worktrees-root", type=Path, default=Path("/opt/experiments"))
    parser.add_argument("--results-root", type=Path, default=Path("/opt/takehome-results"))
    args = parser.parse_args()
    try:
        if Path(command(["git", "rev-parse", "--show-toplevel"])).resolve() != ROOT:
            raise RuntimeError("not running from Git root")
        dirty = command(["git", "status", "--porcelain", "--untracked-files=all"])
        if dirty:
            raise RuntimeError(f"source tree is dirty:\n{dirty}")
        commit = command(["git", "rev-parse", "HEAD"])
        subprocess.run(["git", "merge-base", "--is-ancestor", UPSTREAM_FIX_COMMIT, commit], cwd=ROOT, check=True)
        manifest = args.manifest.resolve()
        if manifest.parent != (ROOT / EXPERIMENT_RELATIVE / "runs").resolve():
            raise RuntimeError("manifest must be a checked-in wave run manifest")
        for run_id in RUNS:
            load_run(ROOT / EXPERIMENT_RELATIVE / "runs" / f"{run_id}.json")
        spec = load_run(manifest)
        validate_env(ROOT / ".env")
        if len(json.loads((ROOT / "sample-problems/manifest.json").read_text())["problems"]) != 16:
            raise RuntimeError("sample set must contain exactly 16 problems")
    except Exception as exc:
        print(f"launcher refusal: {exc}", file=sys.stderr); return 1
    print(f"launcher check passed: run_id={spec.run_id}")
    print(f"commit={commit}")
    if args.check: return 0
    if args.confirm_paid_launch != "I_UNDERSTAND_THIS_LAUNCHES_PAID_RUNS":
        print("launcher refusal: paid-launch confirmation missing", file=sys.stderr); return 2
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    name = f"{spec.run_id}-{stamp}-{commit[:8]}"
    worktree = args.worktrees_root.resolve() / name
    run_root = args.results_root.resolve() / name
    try:
        if worktree.exists() or run_root.exists(): raise RuntimeError("generated target already exists")
        worktree.parent.mkdir(parents=True, exist_ok=True); run_root.mkdir(parents=True); (run_root / "outputs").mkdir()
        shutil.copy2(spec.path, run_root / "run-manifest.json")
        command(["git", "worktree", "add", "--detach", str(worktree), commit], capture=False)
        shutil.copy2(ROOT / ".env", worktree / ".env"); os.chmod(worktree / ".env", 0o600)
        setup_env = dict(os.environ, LEAN_IMAGE=spec.resources["lean_image"])
        subprocess.run(["bash", "scripts/setup.sh"], cwd=worktree, env=setup_env, check=True)
        effective = spec.effective(problems=worktree / "sample-problems", output=run_root / "outputs")
        run_command = [str(worktree / ".venv/bin/python"), str(worktree / "run.py"), "--problems", effective["problems"],
                       "--out", effective["output_root"], "--n-workers", str(effective["n_workers"]), "--agent", effective["agent"]]
        provenance = {"schema_version": 1, "experiment": "baseline-controls-2rep-v1", "run_id": spec.run_id,
                      "condition": spec.condition, "replicate": spec.replicate, "model": spec.model,
                      "launched_at": stamp, "git_commit": commit, "manifest_sha256": spec.manifest_sha256,
                      "sample_manifest_sha256": sha256_file(ROOT / "sample-problems/manifest.json"),
                      "launcher_sha256": sha256_file(ROOT / "scripts/launch_baseline_control.py"),
                      "worktree": str(worktree), "run_root": str(run_root), "command": run_command,
                      "effective_configuration": effective,
                      "host": {"hostname": socket.gethostname(), "platform": platform.platform(),
                               "python": platform.python_version(), "cpu_count": os.cpu_count()}}
        write_json(run_root / "provenance.json", provenance)
        process_env = dict(os.environ); process_env.update(effective["environment"])
        log_path = run_root / "run.log"
        with log_path.open("ab", buffering=0) as log:
            proc = subprocess.Popen(run_command, cwd=worktree, env=process_env, stdin=subprocess.DEVNULL,
                                    stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        (run_root / "run.pid").write_text(f"{proc.pid}\n")
    except BaseException as exc:
        print(f"launch failed; partial artifact preserved at {run_root}: {type(exc).__name__}: {exc}", file=sys.stderr); return 1
    print("baseline/control replication launched")
    for key, value in (("pid", proc.pid), ("commit", commit), ("worktree", worktree), ("run_root", run_root), ("log", log_path), ("provenance", run_root / "provenance.json")):
        print(f"{key}={value}")
    return 0


if __name__ == "__main__": raise SystemExit(main())
