from __future__ import annotations

import pytest

from scripts.dispatch_online_stage2 import validate_worker_allocation


@pytest.mark.parametrize("worker", ["worker-1", "takehome-worker-0", "takehome-worker-11"])
def test_invalid_worker_names_are_rejected(worker):
    with pytest.raises(ValueError, match="invalid worker"):
        validate_worker_allocation({"tasks": [{"task_id": "bad", "worker": worker}]})


def test_all_current_workers_remain_allowed_by_static_validation():
    validate_worker_allocation({
        "tasks": [
            {"task_id": "one", "worker": "takehome-worker-1"},
            {"task_id": "seven", "worker": "takehome-worker-7"},
            {"task_id": "eight", "worker": "takehome-worker-8"},
            {"task_id": "ten", "worker": "takehome-worker-10"},
        ]
    })
