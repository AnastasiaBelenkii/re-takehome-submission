import json

import pytest

from baseline_refresh.experiment import AGENT_SHA256, EXPECTED_CONDITIONS, ManifestError, ROOT, load_condition


def test_frozen_manifests_and_agent_hash():
    for condition_id, model in EXPECTED_CONDITIONS.items():
        condition = load_condition(ROOT / "experiments" / "solo-baseline-refresh-v1" / "conditions" / f"{condition_id}.json")
        assert condition.model == model
        assert condition.resources["n_workers"] == 2
        assert condition.resources["outer_time_s"] == 1200
    assert AGENT_SHA256


def test_manifest_rejects_behavioral_change(tmp_path):
    source = ROOT / "experiments" / "solo-baseline-refresh-v1" / "conditions" / "qwen-solo.json"
    value = json.loads(source.read_text())
    value["resources"]["temperature"] = 0.3
    changed = tmp_path / "qwen-solo.json"
    changed.write_text(json.dumps(value))
    with pytest.raises(ManifestError):
        load_condition(changed)
