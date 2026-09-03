"""Strict condition loading and effective configuration materialization."""

from __future__ import annotations

import hashlib
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from uplift_pilot.constants import DESIGN_ID, MODEL_A, MODEL_B


EXPERIMENT_RELATIVE = Path("experiments/uplift-pilot-v1")
AGENT_REFERENCE = "uplift_pilot.agent:create_agent"
EXPECTED_PROBLEMS = (
    "p03_sq_ge_two_ab",
    "p06_pow_mod",
    "p07_least_divisible",
    "p10_factorial_pow",
    "putnam_2020_a2",
    "rmo_2000_6",
)
EXPECTED_CONDITIONS = {
    "qwen-p": (MODEL_A, "P"),
    "gpt-p": (MODEL_B, "P"),
    "qwen-d": (MODEL_A, "D"),
    "gpt-d": (MODEL_B, "D"),
}
CONDITION_KEYS = {"schema_version", "design_id", "condition", "model", "policy", "resources"}
RESOURCE_KEYS = {
    "outer_time_s",
    "verify_reserve_s",
    "budget_usd",
    "max_calls",
    "generation_max_tokens",
    "planning_max_tokens",
    "temperature",
    "n_workers",
    "max_restarts",
    "diagnostic_chars",
    "failure_memory_chars",
    "lean_check_timeout_s",
    "comparator_timeout_s",
    "lean_image",
}
EXPECTED_RESOURCES = {
    "outer_time_s": 1200,
    "verify_reserve_s": 120,
    "budget_usd": 1.0,
    "max_calls": 25,
    "generation_max_tokens": 12000,
    "planning_max_tokens": 2500,
    "temperature": 0.2,
    "n_workers": 2,
    "max_restarts": 2,
    "diagnostic_chars": 6000,
    "failure_memory_chars": 3000,
    "lean_check_timeout_s": 120,
    "comparator_timeout_s": 180,
    "lean_image": (
        "ghcr.io/verifiedmechanisms/re-takehome-lean"
        "@sha256:ee48287cd31c0a7df572093a879ed7289c2f01fec6c7af8716c605fc8c670c39"
    ),
}


class ConditionError(ValueError):
    pass


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _load_json_object(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ConditionError(f"invalid condition JSON {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise ConditionError("condition must be a JSON object")
    return value


@dataclass(frozen=True)
class Condition:
    path: Path
    condition: str
    model: str
    policy: str
    resources: dict[str, Any]

    @property
    def manifest_sha256(self) -> str:
        return sha256_file(self.path)

    def effective_configuration(self, *, problems_path: Path, output_root: Path) -> dict[str, Any]:
        resource = self.resources
        environment = {
            "LEAN_IMAGE": str(resource["lean_image"]),
            "VM_TIME_LIMIT_S": str(resource["outer_time_s"]),
            "VM_BUDGET_USD": f'{float(resource["budget_usd"]):.2f}',
            "VM_VERIFY_RESERVE_S": str(resource["verify_reserve_s"]),
            "LEAN_CHECK_TIMEOUT_S": str(resource["lean_check_timeout_s"]),
            "COMPARATOR_TIMEOUT_S": str(resource["comparator_timeout_s"]),
            "UPLIFT_DESIGN_ID": DESIGN_ID,
            "UPLIFT_CONDITION": self.condition,
            "UPLIFT_MODEL": self.model,
            "UPLIFT_POLICY": self.policy,
            "UPLIFT_MAX_CALLS": str(resource["max_calls"]),
            "UPLIFT_GENERATION_MAX_TOKENS": str(resource["generation_max_tokens"]),
            "UPLIFT_PLANNING_MAX_TOKENS": str(resource["planning_max_tokens"]),
            "UPLIFT_TEMPERATURE": str(resource["temperature"]),
            "UPLIFT_MAX_RESTARTS": str(resource["max_restarts"]),
            "UPLIFT_DIAGNOSTIC_CHARS": str(resource["diagnostic_chars"]),
            "UPLIFT_FAILURE_MEMORY_CHARS": str(resource["failure_memory_chars"]),
        }
        return {
            "agent": AGENT_REFERENCE,
            "problems": str(problems_path),
            "output_root": str(output_root),
            "n_workers": int(resource["n_workers"]),
            "environment": environment,
        }


def load_condition(path: Path) -> Condition:
    path = path.resolve()
    raw = _load_json_object(path)
    unknown = set(raw) - CONDITION_KEYS
    missing = CONDITION_KEYS - set(raw)
    if unknown or missing:
        raise ConditionError(f"condition fields mismatch; unknown={sorted(unknown)}, missing={sorted(missing)}")
    if raw["schema_version"] != 1:
        raise ConditionError("schema_version must be 1")
    if raw["design_id"] != DESIGN_ID:
        raise ConditionError(f"design_id must be {DESIGN_ID}")
    condition_id = raw["condition"]
    if condition_id not in EXPECTED_CONDITIONS:
        raise ConditionError(f"unknown condition: {condition_id!r}")
    if path.stem != condition_id:
        raise ConditionError(f"condition id {condition_id!r} must match filename {path.name!r}")
    expected_model, expected_policy = EXPECTED_CONDITIONS[condition_id]
    if (raw["model"], raw["policy"]) != (expected_model, expected_policy):
        raise ConditionError(
            f"{condition_id} requires model={expected_model!r}, policy={expected_policy!r}"
        )
    resources = raw["resources"]
    if not isinstance(resources, dict):
        raise ConditionError("resources must be an object")
    unknown_resources = set(resources) - RESOURCE_KEYS
    missing_resources = RESOURCE_KEYS - set(resources)
    if unknown_resources or missing_resources:
        raise ConditionError(
            f"resource fields mismatch; unknown={sorted(unknown_resources)}, missing={sorted(missing_resources)}"
        )
    for key, expected in EXPECTED_RESOURCES.items():
        actual = resources[key]
        if isinstance(expected, float):
            if not isinstance(actual, (int, float)) or not math.isfinite(actual) or float(actual) != expected:
                raise ConditionError(f"resources.{key} must be {expected!r}")
        elif actual != expected:
            raise ConditionError(f"resources.{key} must be {expected!r}")
    if "@sha256:" not in str(resources["lean_image"]):
        raise ConditionError("resources.lean_image must be pinned by digest")
    return Condition(path, condition_id, expected_model, expected_policy, dict(resources))


def load_problem_ids(path: Path) -> tuple[str, ...]:
    try:
        values = tuple(line.strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip())
    except OSError as exc:
        raise ConditionError(f"cannot read problem list {path}: {exc}") from exc
    if values != EXPECTED_PROBLEMS:
        raise ConditionError(
            f"problem list must contain exactly the six predeclared problems in order: {EXPECTED_PROBLEMS}"
        )
    return values
