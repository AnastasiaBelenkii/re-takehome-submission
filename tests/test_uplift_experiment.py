from __future__ import annotations

import json
import subprocess

import pytest

import scripts.collect_uplift_pilot as collector
import scripts.launch_uplift_pilot as launcher
from uplift_pilot.experiment import EXPECTED_CONDITIONS, load_condition


ROOT = launcher.ROOT


def test_all_static_manifests_validate_and_materialize_exact_environment():
    conditions = ROOT / "experiments/uplift-pilot-v1/conditions"
    for condition_id, (model, policy) in EXPECTED_CONDITIONS.items():
        condition = load_condition(conditions / f"{condition_id}.json")
        effective = condition.effective_configuration(problems_path=ROOT / "problems", output_root=ROOT / "out")
        environment = launcher._process_environment(effective, {"UNRELATED": "kept"})
        assert environment["UPLIFT_MODEL"] == model
        assert environment["UPLIFT_POLICY"] == policy
        assert environment["UPLIFT_MAX_CALLS"] == "25"
        assert environment["UNRELATED"] == "kept"
        assert effective["environment"].items() <= environment.items()


def test_manifest_rejects_unknown_key_and_invalid_combination(tmp_path):
    source = ROOT / "experiments/uplift-pilot-v1/conditions/qwen-p.json"
    raw = json.loads(source.read_text())
    raw["unknown"] = True
    bad = tmp_path / "qwen-p.json"
    bad.write_text(json.dumps(raw))
    with pytest.raises(ValueError, match="unknown"):
        load_condition(bad)
    del raw["unknown"]
    raw["policy"] = "D"
    bad.write_text(json.dumps(raw))
    with pytest.raises(ValueError, match="requires"):
        load_condition(bad)


def test_dirty_tree_refusal(tmp_path, monkeypatch):
    subprocess.run(["git", "init", "-q"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.email", "test@example.invalid"], cwd=tmp_path, check=True)
    subprocess.run(["git", "config", "user.name", "Test"], cwd=tmp_path, check=True)
    (tmp_path / "tracked").write_text("clean")
    subprocess.run(["git", "add", "tracked"], cwd=tmp_path, check=True)
    subprocess.run(["git", "commit", "-qm", "initial"], cwd=tmp_path, check=True)
    monkeypatch.setattr(launcher, "ROOT", tmp_path.resolve())
    assert len(launcher._require_clean_source()) == 40
    (tmp_path / "untracked").write_text("dirty")
    with pytest.raises(RuntimeError, match="dirty"):
        launcher._require_clean_source()


def test_existing_launch_targets_are_refused(tmp_path):
    worktree = tmp_path / "worktree"
    result = tmp_path / "result"
    worktree.mkdir()
    with pytest.raises(FileExistsError, match="worktree"):
        launcher._ensure_targets_unused(worktree, result)
    worktree.rmdir()
    result.mkdir()
    with pytest.raises(FileExistsError, match="run directory"):
        launcher._ensure_targets_unused(worktree, result)


def test_collector_derives_safe_remote_name_and_refuses_overwrite(tmp_path, monkeypatch):
    assert collector._bundle_name("worker:/opt/results/qwen-p-run/") == "qwen-p-run"
    existing = tmp_path / "qwen-p-run"
    existing.mkdir()
    monkeypatch.setattr(collector.shutil, "which", lambda _name: "/usr/bin/rsync")
    with pytest.raises(FileExistsError, match="refusing to reuse"):
        collector.collect("worker:/opt/results/qwen-p-run", tmp_path)
