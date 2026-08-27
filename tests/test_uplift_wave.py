from __future__ import annotations

import json

import pytest

import scripts.run_uplift_wave as wave


CELLS = [
    "qwen-p=worker-2",
    "gpt-p=worker-3",
    "qwen-d=worker-4",
    "gpt-d=worker-5b",
]
COMMIT = "a" * 40


def test_cell_mapping_is_exact_and_uses_distinct_hosts():
    parsed = wave._parse_cells(CELLS)
    assert parsed["qwen-p"] == "worker-2"
    with pytest.raises(ValueError, match="exactly"):
        wave._parse_cells(CELLS[:-1])
    with pytest.raises(ValueError, match="distinct"):
        wave._parse_cells(CELLS[:-1] + ["gpt-d=worker-2"])


def test_launch_command_pins_commit_checks_before_launch_and_uses_deploy_key():
    command = wave._launch_command(
        condition="qwen-p",
        commit=COMMIT,
        remote_repo="/root/re-takehome",
        remote_ref="uplift-pilot-v1",
        deploy_key="/root/.ssh/deploy",
    )
    assert "/root/.ssh/deploy" in command
    assert f"git switch --detach {COMMIT}" in command
    assert command.index("--check") < command.rindex("launch_uplift_pilot.py")


def test_launch_output_requires_machine_readable_fields():
    parsed = wave._parse_launch_output(
        f"uplift pilot condition launched\npid=123\ncommit={COMMIT}\n"
        "run_root=/opt/results/run\nlog=/opt/results/run/run.log\n"
    )
    assert parsed["pid"] == 123
    with pytest.raises(ValueError, match="run_root"):
        wave._parse_launch_output(f"pid=123\ncommit={COMMIT}\nlog=/tmp/log")


def test_existing_state_is_resume_only_even_with_no_confirmation(tmp_path):
    state_path = tmp_path / "state.json"
    archive = (tmp_path / "archive").resolve()
    cells = wave._parse_cells(CELLS)
    state = {
        "commit": COMMIT,
        "hosts": cells,
        "archive_root": str(archive),
        "cells": {},
    }
    state_path.write_text(json.dumps(state))
    loaded, is_new = wave._load_or_initialize(
        state_path=state_path,
        commit=COMMIT,
        cells=cells,
        archive_root=archive,
        confirmation=None,
    )
    assert loaded == state
    assert is_new is False


def test_new_state_is_persisted_as_ambiguous_before_dispatch(tmp_path):
    state_path = tmp_path / "state.json"
    archive = tmp_path / "archive"
    cells = wave._parse_cells(CELLS)
    with pytest.raises(ValueError, match="requires --confirm"):
        wave._load_or_initialize(
            state_path=state_path,
            commit=COMMIT,
            cells=cells,
            archive_root=archive,
            confirmation=None,
        )
    state, is_new = wave._load_or_initialize(
        state_path=state_path,
        commit=COMMIT,
        cells=cells,
        archive_root=archive,
        confirmation=wave.CONFIRMATION,
    )
    assert is_new is True
    assert {cell["launch_state"] for cell in state["cells"].values()} == {"dispatched_unknown"}
    assert json.loads(state_path.read_text())["phase"] == "launch_dispatched"
