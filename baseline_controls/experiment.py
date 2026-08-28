"""Strict manifests for the two-replication baseline/control wave."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
EXPERIMENT_ID = "baseline-controls-2rep-v1"
EXPERIMENT_RELATIVE = Path("experiments") / EXPERIMENT_ID
UPSTREAM_FIX_COMMIT = "8739a10c2c94fc9af6cf7eff64b686bf078a295f"
MODEL_A = "qwen/qwen3.5-flash-02-23"
MODEL_B = "openai/gpt-oss-120b"
PINNED_IMAGE = "ghcr.io/verifiedmechanisms/re-takehome-lean@sha256:ee48287cd31c0a7df572093a879ed7289c2f01fec6c7af8716c605fc8c670c39"
RUNS = {
    "qwen-stock-25-r2": ("qwen-stock-25", 2, "baselines.simple_agent:create_agent", MODEL_A, 25),
    "gpt-stock-25-r2": ("gpt-stock-25", 2, "baselines.simple_agent:create_agent", MODEL_B, 25),
    "portfolio-25x2-r2": ("portfolio-25x2", 2, "submission.agent:create_agent", "both", 25),
    "qwen-stock-50-r1": ("qwen-stock-50", 1, "baseline_controls.agent:create_agent", MODEL_A, 50),
    "qwen-stock-50-r2": ("qwen-stock-50", 2, "baseline_controls.agent:create_agent", MODEL_A, 50),
    "gpt-stock-50-r1": ("gpt-stock-50", 1, "baseline_controls.agent:create_agent", MODEL_B, 50),
    "gpt-stock-50-r2": ("gpt-stock-50", 2, "baseline_controls.agent:create_agent", MODEL_B, 50),
}
RESOURCE_KEYS = {
    "outer_time_s", "verify_reserve_s", "budget_usd", "max_turns", "max_tokens",
    "temperature", "n_workers", "lean_check_timeout_s", "comparator_timeout_s", "lean_image",
}
TOP_KEYS = {
    "schema_version", "experiment_id", "run_id", "condition", "replicate", "agent",
    "model", "implementation_sha256", "problem_manifest_sha256", "upstream_fix_commit", "resources",
}


class ManifestError(ValueError):
    pass


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def implementation_path(agent: str, root: Path = ROOT) -> Path:
    module = agent.partition(":")[0]
    return root / Path(*module.split(".")).with_suffix(".py")


@dataclass(frozen=True)
class RunSpec:
    path: Path
    run_id: str
    condition: str
    replicate: int
    agent: str
    model: str
    resources: dict[str, Any]

    @property
    def manifest_sha256(self) -> str:
        return sha256_file(self.path)

    def effective(self, *, problems: Path, output: Path) -> dict[str, Any]:
        r = self.resources
        environment = {
            "LEAN_IMAGE": str(r["lean_image"]), "VM_TIME_LIMIT_S": str(r["outer_time_s"]),
            "VM_BUDGET_USD": f'{float(r["budget_usd"]):.2f}',
            "VM_VERIFY_RESERVE_S": str(r["verify_reserve_s"]),
            "LEAN_CHECK_TIMEOUT_S": str(r["lean_check_timeout_s"]),
            "COMPARATOR_TIMEOUT_S": str(r["comparator_timeout_s"]),
            "BASELINE_MAX_TURNS": str(r["max_turns"]),
            "BASELINE_MAX_TOKENS": str(r["max_tokens"]),
            "BASELINE_TEMPERATURE": str(r["temperature"]),
        }
        if self.model != "both":
            environment["BASELINE_MODEL"] = self.model
        return {"agent": self.agent, "problems": str(problems), "output_root": str(output),
                "n_workers": int(r["n_workers"]), "environment": environment}


def load_run(path: Path, *, root: Path = ROOT) -> RunSpec:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ManifestError(f"invalid manifest {path}: {exc}") from exc
    if not isinstance(raw, dict) or set(raw) != TOP_KEYS:
        raise ManifestError("manifest fields do not match frozen schema")
    run_id = raw["run_id"]
    if raw["schema_version"] != 1 or raw["experiment_id"] != EXPERIMENT_ID:
        raise ManifestError("wrong schema or experiment")
    if run_id not in RUNS or path.stem != run_id:
        raise ManifestError(f"unknown or misnamed run: {run_id!r}")
    expected = RUNS[run_id]
    actual = (raw["condition"], raw["replicate"], raw["agent"], raw["model"], raw["resources"].get("max_turns"))
    if actual != expected:
        raise ManifestError(f"run identity differs: {actual!r} != {expected!r}")
    if raw["upstream_fix_commit"] != UPSTREAM_FIX_COMMIT:
        raise ManifestError("wrong upstream fix commit")
    resources = raw["resources"]
    if not isinstance(resources, dict) or set(resources) != RESOURCE_KEYS:
        raise ManifestError("resource fields do not match frozen schema")
    fixed = {"outer_time_s": 1200, "verify_reserve_s": 120, "budget_usd": 1.0,
             "max_tokens": 12000, "temperature": 0.2, "n_workers": 2,
             "lean_check_timeout_s": 120, "comparator_timeout_s": 180, "lean_image": PINNED_IMAGE}
    for key, value in fixed.items():
        if resources[key] != value:
            raise ManifestError(f"resources.{key} must be {value!r}")
    impl = implementation_path(raw["agent"], root)
    if sha256_file(impl) != raw["implementation_sha256"]:
        raise ManifestError(f"implementation hash mismatch: {impl}")
    problem_manifest = root / "sample-problems" / "manifest.json"
    if sha256_file(problem_manifest) != raw["problem_manifest_sha256"]:
        raise ManifestError("sample manifest hash mismatch")
    return RunSpec(path=path.resolve(), run_id=run_id, condition=raw["condition"],
                   replicate=raw["replicate"], agent=raw["agent"], model=raw["model"], resources=dict(resources))
