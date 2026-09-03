"""Strict v2 condition/profile manifests and frozen queue construction."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .constants import CONDITIONS, CORE_PROBLEMS, DATASET_DEFECTS, DEEP_PROBLEMS, DESIGN_ID
from .strategies import create_strategy

EXPERIMENT_RELATIVE = Path("experiments/collaboration-engine-v2")
AGENT_REFERENCE = "collaboration_engine_v2.agent:create_agent"
EXPECTED_STRATEGIES = {
    "c0": "none", "c1": "reciprocal-once-v1", "c2": "reciprocal-every-eligible-v1",
}
SHALLOW = {
    "outer_time_s": 1680, "verify_reserve_s": 180, "dispatch_cutoff_s": 960,
    "budget_usd": 1.0, "max_calls_per_model": 25,
    "generation_max_tokens": 12000, "temperature": 0.2, "max_restarts": 2,
    "diagnostic_chars": 6000, "failure_memory_chars": 3000,
    "peer_packet_chars": 6000, "lean_check_timeout_s": 120,
    "comparator_timeout_s": 180, "max_cost_free_429_retries": 2,
}
DEEP = {
    **SHALLOW, "outer_time_s": 28800, "verify_reserve_s": 180,
    "dispatch_cutoff_s": 28080, "max_calls_per_model": None,
}
SEEDS = (1729, 2718, 3141)
LEAN_IMAGE = "ghcr.io/verifiedmechanisms/re-takehome-lean@sha256:ee48287cd31c0a7df572093a879ed7289c2f01fec6c7af8716c605fc8c670c39"


@dataclass(frozen=True)
class Condition:
    path: Path
    condition: str
    strategy: str


@dataclass(frozen=True)
class Task:
    task_id: str
    stage: str
    profile: str
    problem: str
    replication: int
    seed: int
    condition: str
    strategy: str


def load_condition(path: Path) -> Condition:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if set(raw) != {"schema_version", "design_id", "condition", "collaboration_strategy"}:
        raise ValueError("condition manifest fields do not match the frozen schema")
    condition = raw.get("condition")
    if raw.get("schema_version") != 1 or raw.get("design_id") != DESIGN_ID:
        raise ValueError("condition manifest identity is invalid")
    if condition not in CONDITIONS or path.stem != condition:
        raise ValueError("unknown or misnamed condition")
    strategy = raw.get("collaboration_strategy")
    if strategy != EXPECTED_STRATEGIES[condition]:
        raise ValueError("condition has the wrong strategy")
    create_strategy(strategy, packet_chars=SHALLOW["peer_packet_chars"])
    return Condition(path.resolve(), condition, strategy)


def load_resources(path: Path) -> dict[str, dict[str, Any]]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if raw != {"schema_version": 1, "design_id": DESIGN_ID, "lean_image": LEAN_IMAGE,
               "profiles": {"shallow": SHALLOW, "deep": DEEP}}:
        raise ValueError("resource manifest differs from the frozen contract")
    return {"shallow": dict(SHALLOW), "deep": dict(DEEP)}


def build_queue(conditions: dict[str, Condition]) -> list[Task]:
    tasks: list[Task] = []
    # Sentinel first, with its three arms adjacent and concurrent.
    for condition in CONDITIONS:
        item = conditions[condition]
        tasks.append(Task(f"sentinel-rmo_2000_2-r1-{condition}", "sentinel", "shallow",
                          "rmo_2000_2", 1, SEEDS[0], condition, item.strategy))
    # Frozen Latin-style rotation: within every problem/rep block the leading arm rotates.
    for replication, seed in enumerate(SEEDS, 1):
        for problem_index, problem in enumerate(CORE_PROBLEMS):
            for offset in range(3):
                condition = CONDITIONS[(problem_index + replication - 1 + offset) % 3]
                if problem == "rmo_2000_2" and replication == 1:
                    continue
                item = conditions[condition]
                tasks.append(Task(f"core-{problem}-r{replication}-{condition}", "core", "shallow",
                                  problem, replication, seed, condition, item.strategy))
    valid = [
        "p01_linear", "p02_frac_cancel", "p04_sum_sq", "p05_gcd_mersenne",
        "p08_sum_products", "p09_imo1964", "rmo_2001_2", "rmo_2000_3",
        "putnam_2018_a1",
    ]
    for problem_index, problem in enumerate(valid):
        for offset in range(3):
            condition = CONDITIONS[(problem_index + offset) % 3]
            item = conditions[condition]
            tasks.append(Task(f"breadth-{problem}-r1-{condition}", "breadth", "shallow",
                              problem, 1, SEEDS[0], condition, item.strategy))
    for problem in DEEP_PROBLEMS:
        for condition in CONDITIONS:
            item = conditions[condition]
            tasks.append(Task(f"deep-{problem}-r1-{condition}", "deep", "deep",
                              problem, 1, SEEDS[0], condition, item.strategy))
    assert len(tasks) == 87 and DATASET_DEFECTS == ("rmo_2000_6",)
    return tasks


def effective_environment(task: Task, resources: dict[str, Any], lean_image: str) -> dict[str, str]:
    ceiling = resources["max_calls_per_model"]
    return {
        "LEAN_IMAGE": lean_image, "VM_TIME_LIMIT_S": str(resources["outer_time_s"]),
        "VM_VERIFY_RESERVE_S": str(resources["verify_reserve_s"]),
        "VM_BUDGET_USD": f'{resources["budget_usd"]:.2f}',
        "LEAN_CHECK_TIMEOUT_S": str(resources["lean_check_timeout_s"]),
        "COMPARATOR_TIMEOUT_S": str(resources["comparator_timeout_s"]),
        "COLLAB_DESIGN_ID": DESIGN_ID, "COLLAB_CONDITION": task.condition,
        "COLLAB_STRATEGY": task.strategy, "COLLAB_SEED": str(task.seed),
        "COLLAB_MAX_CALLS_PER_MODEL": "unlimited" if ceiling is None else str(ceiling),
        "COLLAB_GENERATION_MAX_TOKENS": str(resources["generation_max_tokens"]),
        "COLLAB_TEMPERATURE": str(resources["temperature"]),
        "COLLAB_MAX_RESTARTS": str(resources["max_restarts"]),
        "COLLAB_DIAGNOSTIC_CHARS": str(resources["diagnostic_chars"]),
        "COLLAB_FAILURE_MEMORY_CHARS": str(resources["failure_memory_chars"]),
        "COLLAB_PEER_PACKET_CHARS": str(resources["peer_packet_chars"]),
        "COLLAB_DISPATCH_CUTOFF_S": str(resources["dispatch_cutoff_s"]),
        "COLLAB_MAX_FREE_429_RETRIES": str(resources["max_cost_free_429_retries"]),
        "COLLAB_MODEL_CALL_WALL_TIMEOUT_S": str(
            resources.get("model_call_wall_timeout_s", 420)
        ),
    }
