from __future__ import annotations

import pytest

from scripts.dispatch_online_stage2 import validate_worker_allocation


def test_worker_ten_is_coordinator_only():
    with pytest.raises(ValueError, match="coordinator-only.*takehome-worker-10"):
        validate_worker_allocation({
            "tasks": [{"task_id": "bad", "worker": "takehome-worker-10"}]
        })


def test_experiment_workers_remain_allowed():
    validate_worker_allocation({
        "tasks": [
            {"task_id": "one", "worker": "takehome-worker-1"},
            {"task_id": "nine", "worker": "takehome-worker-9"},
        ]
    })
