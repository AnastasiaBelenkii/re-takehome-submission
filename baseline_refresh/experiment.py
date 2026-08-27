"""Strict manifests for byte-preserving reruns of the supplied solo baseline."""

from __future__ import annotations

import hashlib
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
EXPERIMENT_ID = "solo-baseline-refresh-v1"
EXPERIMENT_RELATIVE = Path("experiments") / EXPERIMENT_ID
AGENT_REFERENCE = "baselines.simple_agent:create_agent"
AGENT_SHA256 = "21777b15767fe677fa0d375506a32633c8eeb86683ee0853e2ea5e0b23003607"
PROBLEM_MANIFEST_SHA256 = "93048c424cab180abd699d0aa4754d8a402eea79d10240409cb93f1cfa088440"
UPSTREAM_FIX_COMMIT = "8739a10c2c94fc9af6cf7eff64b686bf078a295f"
MODEL_A = "qwen/qwen3.5-flash-02-23"
MODEL_B = "openai/gpt-oss-120b"
EXPECTED_CONDITIONS = {
    "qwen-solo": MODEL_A,
    "gpt-solo": MODEL_B,
}
EXPECTED_RESOURCES = {
    "outer_time_s": 1200,
    "verify_reserve_s": 120,
    "budget_usd": 1.0,
    "max_turns": 25,
    "max_tokens": 12000,
    "temperature": 0.2,
    "n_workers": 2,
    "lean_check_timeout_s": 120,
    "comparator_timeout_s": 180,
    "lean_image": (
        "ghcr.io/verifiedmechanisms/re-takehome-lean"
        "@sha256:ee48287cd31c0a7df572093a879ed7289c2f01fec6c7af8716c605fc8c670c39"
    ),
}
TOP_LEVEL_KEYS = {
    "schema_version",
    "experiment_id",
    "condition",
    "model",
    "agent",
    "agent_sha256",
    "problem_manifest_sha256",
    "upstream_fix_commit",
    "resources",
}


class ManifestError(ValueError):
    pass


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


@dataclass(frozen=True)
class Condition:
    path: Path
    condition: str
    model: str
    resources: dict[str, Any]

    @property
    def manifest_sha256(self) -> str:
        return sha256_file(self.path)

    def environment(self) -> dict[str, str]:
        resource = self.resources
        return {
            "LEAN_IMAGE": str(resource["lean_image"]),
            "VM_TIME_LIMIT_S": str(resource["outer_time_s"]),
            "VM_BUDGET_USD": f'{float(resource["budget_usd"]):.2f}',
            "VM_VERIFY_RESERVE_S": str(resource["verify_reserve_s"]),
            "LEAN_CHECK_TIMEOUT_S": str(resource["lean_check_timeout_s"]),
            "COMPARATOR_TIMEOUT_S": str(resource["comparator_timeout_s"]),
            "BASELINE_MODEL": self.model,
            "BASELINE_MAX_TURNS": str(resource["max_turns"]),
            "BASELINE_MAX_TOKENS": str(resource["max_tokens"]),
            "BASELINE_TEMPERATURE": str(resource["temperature"]),
        }


def load_condition(path: Path, *, root: Path = ROOT) -> Condition:
    path = path.resolve()
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ManifestError(f"invalid manifest {path}: {exc}") from exc
    if not isinstance(raw, dict) or set(raw) != TOP_LEVEL_KEYS:
        raise ManifestError("manifest top-level fields do not match the frozen schema")
    if raw["schema_version"] != 1 or raw["experiment_id"] != EXPERIMENT_ID:
        raise ManifestError("manifest schema or experiment id is incorrect")
    condition = raw["condition"]
    if condition not in EXPECTED_CONDITIONS or path.stem != condition:
        raise ManifestError(f"unknown or misnamed condition: {condition!r}")
    if raw["model"] != EXPECTED_CONDITIONS[condition]:
        raise ManifestError(f"wrong model for {condition}")
    expected_literals = {
        "agent": AGENT_REFERENCE,
        "agent_sha256": AGENT_SHA256,
        "problem_manifest_sha256": PROBLEM_MANIFEST_SHA256,
        "upstream_fix_commit": UPSTREAM_FIX_COMMIT,
    }
    for key, expected in expected_literals.items():
        if raw[key] != expected:
            raise ManifestError(f"{key} must be {expected!r}")
    resources = raw["resources"]
    if not isinstance(resources, dict) or set(resources) != set(EXPECTED_RESOURCES):
        raise ManifestError("resource fields do not match the frozen schema")
    for key, expected in EXPECTED_RESOURCES.items():
        actual = resources[key]
        if isinstance(expected, float):
            if not isinstance(actual, (int, float)) or not math.isfinite(actual) or float(actual) != expected:
                raise ManifestError(f"resources.{key} must be {expected!r}")
        elif actual != expected:
            raise ManifestError(f"resources.{key} must be {expected!r}")
    if sha256_file(root / "baselines" / "simple_agent.py") != AGENT_SHA256:
        raise ManifestError("supplied baseline agent is not byte-identical to the pinned upstream version")
    if sha256_file(root / "sample-problems" / "manifest.json") != PROBLEM_MANIFEST_SHA256:
        raise ManifestError("sample problem manifest is not byte-identical to the pinned version")
    return Condition(path=path, condition=condition, model=raw["model"], resources=dict(resources))
