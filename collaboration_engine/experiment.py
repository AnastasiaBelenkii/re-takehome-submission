"""Strict manifests for the factorized collaboration experiment."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .constants import DESIGN_ID
from .strategies import create_strategy


EXPERIMENT_RELATIVE = Path("experiments/collaboration-engine-v1")
AGENT_REFERENCE = "collaboration_engine.agent:create_agent"
EXPECTED_CONDITIONS = {
    "hd-none": "none",
    "hd-reciprocal": "reciprocal-cross-repair-v1",
}
EXPECTED_RESOURCES = {
    "outer_time_s": 1200,
    "verify_reserve_s": 120,
    "budget_usd": 1.0,
    "max_calls_per_model": 25,
    "generation_max_tokens": 12000,
    "temperature": 0.2,
    "n_workers": 2,
    "max_restarts": 2,
    "diagnostic_chars": 6000,
    "failure_memory_chars": 3000,
    "peer_packet_chars": 6000,
    "lean_check_timeout_s": 120,
    "comparator_timeout_s": 180,
    "lean_image": "ghcr.io/verifiedmechanisms/re-takehome-lean@sha256:ee48287cd31c0a7df572093a879ed7289c2f01fec6c7af8716c605fc8c670c39",
}


@dataclass(frozen=True)
class Condition:
    path: Path
    condition: str
    strategy: str
    resources: dict[str, Any]

    def effective_configuration(self, *, problems_path: Path, output_root: Path) -> dict[str, Any]:
        resource = self.resources
        return {
            "agent": AGENT_REFERENCE,
            "problems": str(problems_path),
            "output_root": str(output_root),
            "n_workers": resource["n_workers"],
            "environment": {
                "LEAN_IMAGE": resource["lean_image"],
                "VM_TIME_LIMIT_S": str(resource["outer_time_s"]),
                "VM_VERIFY_RESERVE_S": str(resource["verify_reserve_s"]),
                "VM_BUDGET_USD": f'{resource["budget_usd"]:.2f}',
                "LEAN_CHECK_TIMEOUT_S": str(resource["lean_check_timeout_s"]),
                "COMPARATOR_TIMEOUT_S": str(resource["comparator_timeout_s"]),
                "COLLAB_DESIGN_ID": DESIGN_ID,
                "COLLAB_CONDITION": self.condition,
                "COLLAB_STRATEGY": self.strategy,
                "COLLAB_MAX_CALLS_PER_MODEL": str(resource["max_calls_per_model"]),
                "COLLAB_GENERATION_MAX_TOKENS": str(resource["generation_max_tokens"]),
                "COLLAB_TEMPERATURE": str(resource["temperature"]),
                "COLLAB_MAX_RESTARTS": str(resource["max_restarts"]),
                "COLLAB_DIAGNOSTIC_CHARS": str(resource["diagnostic_chars"]),
                "COLLAB_FAILURE_MEMORY_CHARS": str(resource["failure_memory_chars"]),
                "COLLAB_PEER_PACKET_CHARS": str(resource["peer_packet_chars"]),
            },
        }


def load_condition(path: Path) -> Condition:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if set(raw) != {"schema_version", "design_id", "condition", "uplift_policy", "collaboration_strategy", "resources"}:
        raise ValueError("condition manifest fields do not match the frozen schema")
    if raw["schema_version"] != 1 or raw["design_id"] != DESIGN_ID or raw["uplift_policy"] != "H+D":
        raise ValueError("condition manifest identity is invalid")
    condition = raw["condition"]
    if condition not in EXPECTED_CONDITIONS or path.stem != condition:
        raise ValueError(f"unknown or misnamed condition: {condition!r}")
    if raw["collaboration_strategy"] != EXPECTED_CONDITIONS[condition]:
        raise ValueError("condition has the wrong collaboration strategy")
    if raw["resources"] != EXPECTED_RESOURCES:
        raise ValueError("condition resources differ from the frozen shared contract")
    create_strategy(raw["collaboration_strategy"], packet_chars=raw["resources"]["peer_packet_chars"])
    return Condition(path.resolve(), condition, raw["collaboration_strategy"], dict(raw["resources"]))
