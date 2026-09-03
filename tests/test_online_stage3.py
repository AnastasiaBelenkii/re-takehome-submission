from __future__ import annotations

import json
from pathlib import Path

from scripts.control_online_stage3 import build_tasks


ROOT = Path(__file__).resolve().parents[1]


def tasks():
    plan = json.loads(
        (ROOT / "experiments/online-development-v1/stage3-replication-v1.json").read_text()
    )
    return plan, build_tasks(plan)


def test_stage3_is_three_by_six_core_plus_one_by_ten_breadth():
    _plan, queue = tasks()
    assert len(queue) == 84
    assert sum(task.stage == "core" for task in queue) == 54
    assert sum(task.stage == "breadth" for task in queue) == 30
    assert "rmo_2000_6" in {task.problem for task in queue}


def test_every_block_is_a_matched_condition_trio():
    _plan, queue = tasks()
    blocks = {task.block_id for task in queue}
    assert len(blocks) == 28
    for block_id in blocks:
        block = [task for task in queue if task.block_id == block_id]
        assert len(block) == 3
        assert {task.condition for task in block} == {"c0", "c1", "c2"}
        assert len({task.worker for task in block}) == 3


def test_stage3_uses_all_and_only_workers_one_through_nine():
    _plan, queue = tasks()
    assert {task.worker for task in queue} == {
        f"takehome-worker-{index}" for index in range(1, 10)
    }
    assert all(task.worker != "takehome-worker-10" for task in queue)


def test_condition_to_worker_mapping_rotates_within_each_group():
    _plan, queue = tasks()
    mappings = {
        group: {
            tuple((task.condition, task.worker) for task in queue if task.block_id == block_id)
            for block_id in {task.block_id for task in queue if task.group == group}
        }
        for group in range(3)
    }
    assert all(len(group_mappings) == 3 for group_mappings in mappings.values())
