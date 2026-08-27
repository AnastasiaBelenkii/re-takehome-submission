#!/usr/bin/env python3
"""Launch and finish the four-cell uplift wave without automatic paid retries.

Run this inside tmux. The state file is written before any launch is dispatched.
If the controller is interrupted, invoke the identical command again: an
existing state file switches it permanently into resume-only mode.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import shlex
import subprocess
import sys
import time
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
for import_root in (ROOT / "src", ROOT):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from scripts.analyze_uplift_pilot import analyze
from scripts.collect_uplift_pilot import _bundle_name, collect
from uplift_pilot.experiment import EXPECTED_CONDITIONS
from uplift_pilot.validation import append_ledger, validate_bundle, write_validation_artifacts


CONFIRMATION = "I_UNDERSTAND_THIS_LAUNCHES_PAID_RUNS"
TERMINAL_REMOTE_STATES = frozenset({"complete", "exited_incomplete"})


def _utc_now() -> str:
    return datetime.now(UTC).isoformat()


def _atomic_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def _parse_cells(values: list[str]) -> dict[str, str]:
    cells: dict[str, str] = {}
    for value in values:
        condition, separator, host = value.partition("=")
        if not separator or not condition or not host:
            raise ValueError(f"invalid --cell {value!r}; expected CONDITION=SSH_HOST")
        if condition in cells:
            raise ValueError(f"duplicate condition in --cell: {condition}")
        if not re.fullmatch(r"[A-Za-z0-9._-]+", host):
            raise ValueError(f"unsafe SSH host alias: {host!r}")
        cells[condition] = host
    if set(cells) != set(EXPECTED_CONDITIONS):
        raise ValueError(f"--cell conditions must be exactly {sorted(EXPECTED_CONDITIONS)}")
    if len(set(cells.values())) != len(cells):
        raise ValueError("each condition must use a distinct SSH host")
    return cells


def _ssh_argv(host: str, remote_command: str) -> list[str]:
    return ["ssh", "-o", "BatchMode=yes", host, "bash", "-lc", shlex.quote(remote_command)]


def _launch_command(
    *, condition: str, commit: str, remote_repo: str, remote_ref: str, deploy_key: str
) -> str:
    condition_path = f"experiments/uplift-pilot-v1/conditions/{condition}.json"
    git_ssh = (
        f"ssh -i {shlex.quote(deploy_key)} -o IdentitiesOnly=yes "
        "-o StrictHostKeyChecking=accept-new"
    )
    commands = [
        "set -euo pipefail",
        f"cd {shlex.quote(remote_repo)}",
        f"GIT_SSH_COMMAND={shlex.quote(git_ssh)} git fetch origin {shlex.quote(remote_ref)}",
        f"git cat-file -e {shlex.quote(commit + '^{commit}')}",
        f"git switch --detach {shlex.quote(commit)}",
        f"test \"$(git rev-parse HEAD)\" = {shlex.quote(commit)}",
        f"python3 scripts/launch_uplift_pilot.py {shlex.quote(condition_path)} --check",
        f"python3 scripts/launch_uplift_pilot.py {shlex.quote(condition_path)}",
    ]
    return "\n".join(commands)


def _parse_launch_output(output: str) -> dict[str, Any]:
    fields: dict[str, str] = {}
    for line in output.splitlines():
        key, separator, value = line.partition("=")
        if separator and key in {"pid", "commit", "worktree", "run_root", "log", "provenance"}:
            fields[key] = value.strip()
    for required in ("pid", "commit", "run_root", "log"):
        if not fields.get(required):
            raise ValueError(f"launcher output is missing {required}=...")
    fields["pid"] = int(fields["pid"])
    return fields


def _run_ssh(host: str, command: str) -> str:
    result = subprocess.run(
        _ssh_argv(host, command), check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT
    )
    return result.stdout


def _poll_remote(host: str, run_root: str, pid: int) -> dict[str, Any]:
    code = """import json, os, pathlib, sys
root = pathlib.Path(sys.argv[1])
pid = int(sys.argv[2])
run_paths = list((root / 'outputs').rglob('run.json')) if (root / 'outputs').is_dir() else []
finished = False
if len(run_paths) == 1:
    try:
        run = json.loads(run_paths[0].read_text())
        summary = json.loads((run_paths[0].parent / 'summary.json').read_text())
        finished = bool(run.get('finished_at')) and bool(summary.get('finished_at'))
    except (OSError, json.JSONDecodeError):
        pass
alive = True
try:
    os.kill(pid, 0)
except (ProcessLookupError, PermissionError):
    alive = False
state = 'complete' if finished else ('running' if alive else 'exited_incomplete')
print(json.dumps({'state': state, 'run_json_count': len(run_paths), 'pid_alive': alive}))
"""
    remote = "python3 -c {} {} {}".format(
        shlex.quote(code), shlex.quote(run_root), shlex.quote(str(pid))
    )
    output = _run_ssh(host, remote)
    value = json.loads(output.strip().splitlines()[-1])
    if value.get("state") not in TERMINAL_REMOTE_STATES | {"running"}:
        raise ValueError(f"unexpected remote state: {value!r}")
    return value


def _load_or_initialize(
    *, state_path: Path, commit: str, cells: dict[str, str], archive_root: Path, confirmation: str | None
) -> tuple[dict[str, Any], bool]:
    if state_path.exists():
        state = json.loads(state_path.read_text(encoding="utf-8"))
        expected = {"commit": commit, "hosts": cells, "archive_root": str(archive_root.resolve())}
        for key, value in expected.items():
            if state.get(key) != value:
                raise ValueError(f"existing state {key} differs; refusing ambiguous resume")
        return state, False
    if confirmation != CONFIRMATION:
        raise ValueError(f"new wave requires --confirm-paid-launch {CONFIRMATION}")
    state = {
        "schema_version": 1,
        "created_at": _utc_now(),
        "updated_at": _utc_now(),
        "commit": commit,
        "hosts": cells,
        "archive_root": str(archive_root.resolve()),
        "phase": "launch_dispatched",
        # Persist ambiguity before dispatch: a resumed controller must never
        # accidentally repeat a paid launch whose response it did not receive.
        "cells": {
            condition: {"host": host, "launch_state": "dispatched_unknown"}
            for condition, host in cells.items()
        },
    }
    _atomic_json(state_path, state)
    return state, True


def _ledger_contains(ledger: Path, bundle: Path) -> bool:
    if not ledger.exists():
        return False
    for line in ledger.read_text(encoding="utf-8").splitlines():
        entry = json.loads(line)
        if entry.get("artifact_path") == str(bundle.resolve()):
            return True
    return False


def _save(state_path: Path, state: dict[str, Any]) -> None:
    state["updated_at"] = _utc_now()
    _atomic_json(state_path, state)


def run(args: argparse.Namespace) -> int:
    if not re.fullmatch(r"[0-9a-f]{40}", args.commit):
        raise ValueError("--commit must be a full lowercase 40-character Git SHA")
    cells = _parse_cells(args.cell)
    archive_root = args.archive_root.resolve()
    state_path = args.state.resolve()
    state, is_new = _load_or_initialize(
        state_path=state_path,
        commit=args.commit,
        cells=cells,
        archive_root=archive_root,
        confirmation=args.confirm_paid_launch,
    )

    if is_new:
        print(f"state persisted before paid dispatch: {state_path}", flush=True)
        def launch_one(item: tuple[str, str]) -> tuple[str, str, str]:
            condition, host = item
            command = _launch_command(
                condition=condition,
                commit=args.commit,
                remote_repo=args.remote_repo,
                remote_ref=args.remote_ref,
                deploy_key=args.remote_deploy_key,
            )
            try:
                return condition, "launched", _run_ssh(host, command)
            except subprocess.CalledProcessError as exc:
                return condition, "failed_or_unknown", exc.stdout or str(exc)

        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
            results = list(executor.map(launch_one, cells.items()))
        for condition, launch_state, output in results:
            cell = state["cells"][condition]
            cell["launch_output"] = output[-12000:]
            cell["launch_state"] = launch_state
            if launch_state == "launched":
                try:
                    details = _parse_launch_output(output)
                    if details["commit"] != args.commit:
                        raise ValueError("remote launcher reported the wrong commit")
                    cell.update(details)
                except (ValueError, TypeError) as exc:
                    cell["launch_state"] = "failed_or_unknown"
                    cell["launch_parse_error"] = str(exc)
            print(f"{condition}: {cell['launch_state']}", flush=True)
        state["phase"] = "monitoring"
        _save(state_path, state)
    else:
        print(f"resuming existing state without launching: {state_path}", flush=True)

    monitorable = {
        condition: cell for condition, cell in state["cells"].items()
        if cell.get("run_root") and cell.get("pid")
    }
    if len(monitorable) != len(EXPECTED_CONDITIONS):
        state["phase"] = "manual_intervention_required"
        _save(state_path, state)
        print("one or more paid launch outcomes are unknown; refusing automatic retry", file=sys.stderr)
        return 2

    deadline = time.monotonic() + args.wait_timeout_seconds
    while True:
        unfinished = [
            (condition, cell) for condition, cell in monitorable.items()
            if cell.get("remote_state") not in TERMINAL_REMOTE_STATES
        ]
        if not unfinished:
            break

        def poll_one(item: tuple[str, dict[str, Any]]) -> tuple[str, dict[str, Any]]:
            condition, cell = item
            try:
                return condition, _poll_remote(cell["host"], cell["run_root"], int(cell["pid"]))
            except (subprocess.CalledProcessError, ValueError, json.JSONDecodeError) as exc:
                return condition, {"state": "poll_error", "error": str(exc)}

        with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
            poll_results = list(executor.map(poll_one, unfinished))
        for condition, result in poll_results:
            cell = state["cells"][condition]
            if result["state"] != "poll_error":
                cell["remote_state"] = result["state"]
            cell["last_poll"] = {**result, "at": _utc_now()}
            print(f"{condition}: {result['state']}", flush=True)
        _save(state_path, state)
        if all(cell.get("remote_state") in TERMINAL_REMOTE_STATES for cell in monitorable.values()):
            break
        if time.monotonic() >= deadline:
            state["phase"] = "monitor_timeout"
            _save(state_path, state)
            print("monitor timeout reached; remote runs were not killed and may be resumed later", file=sys.stderr)
            return 3
        time.sleep(args.poll_seconds)

    state["phase"] = "collecting"
    _save(state_path, state)
    bundles_root = archive_root / "bundles"
    ledger = archive_root / "runs.jsonl"
    valid_bundles: list[Path] = []
    for condition, cell in state["cells"].items():
        source = f"{cell['host']}:{cell['run_root']}"
        bundle = bundles_root / _bundle_name(source)
        try:
            if not bundle.is_dir():
                bundle = collect(source, bundles_root)
            validation = validate_bundle(
                bundle,
                expected_condition_path=ROOT / "experiments/uplift-pilot-v1/conditions" / f"{condition}.json",
                expected_commit=args.commit,
            )
            write_validation_artifacts(bundle, validation)
            provenance = json.loads((bundle / "provenance.json").read_text(encoding="utf-8"))
            if not _ledger_contains(ledger, bundle):
                append_ledger(ledger, validation, provenance)
            cell["bundle"] = str(bundle)
            cell["validation_passed"] = validation.valid
            cell["validation_errors"] = list(validation.errors)
            if validation.valid:
                valid_bundles.append(bundle)
            print(f"{condition}: collected; valid={validation.valid}", flush=True)
        except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError, json.JSONDecodeError) as exc:
            cell["collection_error"] = str(exc)
            print(f"{condition}: collection/validation failed: {exc}", file=sys.stderr, flush=True)
        _save(state_path, state)

    if len(valid_bundles) == len(EXPECTED_CONDITIONS):
        report = analyze(valid_bundles)
        analysis_path = archive_root / "analysis.json"
        _atomic_json(analysis_path, report)
        state["phase"] = "complete"
        state["analysis"] = str(analysis_path)
        _save(state_path, state)
        print(f"wave complete: {analysis_path}")
        return 0

    state["phase"] = "invalid_or_incomplete"
    _save(state_path, state)
    print("wave preserved, but not all four bundles are valid", file=sys.stderr)
    return 4


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--state", type=Path, required=True)
    parser.add_argument("--archive-root", type=Path, required=True)
    parser.add_argument("--cell", action="append", default=[], metavar="CONDITION=SSH_HOST")
    parser.add_argument("--remote-repo", default="/root/re-takehome")
    parser.add_argument("--remote-ref", default="uplift-pilot-v1")
    parser.add_argument("--remote-deploy-key", default="/root/.ssh/re_takehome_deploy")
    parser.add_argument("--poll-seconds", type=float, default=30.0)
    parser.add_argument("--wait-timeout-seconds", type=float, default=10800.0)
    parser.add_argument("--confirm-paid-launch")
    args = parser.parse_args(argv)
    if args.poll_seconds < 1 or args.wait_timeout_seconds < 1:
        parser.error("poll and wait timeouts must be at least one second")
    try:
        return run(args)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"controller refusal: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
