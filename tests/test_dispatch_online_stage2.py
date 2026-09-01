from __future__ import annotations

import pytest

from scripts.dispatch_online_stage2 import validate_worker_allocation


@pytest.mark.parametrize("worker", [
    "takehome-worker-8",
    "takehome-worker-9",
    "takehome-worker-10",
])
def test_human_and_coordinator_hosts_are_not_experiment_workers(worker):
    with pytest.raises(ValueError, match="reserved non-experiment"):
        validate_worker_allocation({"tasks": [{"task_id": "bad", "worker": worker}]})


def test_experiment_workers_remain_allowed():
    validate_worker_allocation({
        "tasks": [
            {"task_id": "one", "worker": "takehome-worker-1"},
            {"task_id": "seven", "worker": "takehome-worker-7"},
        ]
    })
