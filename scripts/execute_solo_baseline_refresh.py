#!/usr/bin/env python3
"""Execute both frozen solo-baseline manifests sequentially in one worktree."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
for import_root in (ROOT / "src", ROOT):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from baseline_refresh.experiment import AGENT_REFERENCE, EXPECTED_CONDITIONS, EXPERIMENT_RELATIVE, load_condition


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _write(path: Path, value: object) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-root", type=Path, required=True)
    args = parser.parse_args(argv)
    run_root = args.run_root.resolve()
    state_path = run_root / "state.json"
    state = json.loads(state_path.read_text(encoding="utf-8"))
    python = ROOT / ".venv" / "bin" / "python"
    overall_ok = True

    for condition_id in EXPECTED_CONDITIONS:
        manifest = ROOT / EXPERIMENT_RELATIVE / "conditions" / f"{condition_id}.json"
        condition = load_condition(manifest, root=ROOT)
        cell_root = run_root / condition_id
        output_root = cell_root / "outputs"
        output_root.mkdir(parents=True, exist_ok=False)
        command = [
            str(python),
            str(ROOT / "run.py"),
            "--problems",
            str(ROOT / "sample-problems"),
            "--out",
            str(output_root),
            "--n-workers",
            str(condition.resources["n_workers"]),
            "--agent",
            AGENT_REFERENCE,
        ]
        cell = state["conditions"][condition_id]
        cell.update({"started_at": _now(), "command": command, "state": "running"})
        _write(state_path, state)
        environment = dict(os.environ)
        environment.update(condition.environment())
        result = subprocess.run(command, cwd=ROOT, env=environment)
        cell.update({"finished_at": _now(), "exit_code": result.returncode, "state": "finished"})
        _write(state_path, state)
        if result.returncode != 0:
            overall_ok = False

    state["finished_at"] = _now()
    state["state"] = "finished" if overall_ok else "finished_with_errors"
    _write(state_path, state)
    return 0 if overall_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
