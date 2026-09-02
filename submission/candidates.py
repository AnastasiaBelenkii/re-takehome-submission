"""Self-contained candidate factories for judge-path rehearsals.

These factories make each experimental arm runnable without the COLLAB_* identity
variables used by experiment dispatch. Promotion remains an explicit one-line
choice in ``submission.agent`` after comparative results are reviewed.
"""

from __future__ import annotations

import os
from dataclasses import dataclass
from typing import Callable

from collaboration_engine_v2.agent import CollaborationEngineV2Agent
from collaboration_engine_v2.constants import MODELS
from collaboration_engine_v2.strategies import create_strategy


@dataclass(frozen=True)
class Candidate:
    condition: str
    strategy: str
    salvage: bool
    fast_track_reserved_calls: int


CANDIDATES = {
    "c0": Candidate("c0", "none", False, 0),
    "c1": Candidate("c1", "reciprocal-once-v1", False, 0),
    "c2": Candidate("c2", "reciprocal-every-eligible-v1", False, 0),
    "c0plus-reserve": Candidate("c0plus-reserve", "none", True, 1),
    "c1plus-fill-reserve": Candidate(
        "c1plus-fill-reserve", "progress-fill-event-latest-v2", True, 1
    ),
}


def _integer(name: str, default: int) -> int:
    try:
        return int(os.environ.get(name, str(default)))
    except ValueError as exc:
        raise ValueError(f"{name} must be an integer") from exc


def create_candidate(condition: str) -> CollaborationEngineV2Agent:
    spec = CANDIDATES[condition]
    time_limit = _integer("VM_TIME_LIMIT_S", 28800)
    raw_ceiling = os.environ.get("COLLAB_MAX_CALLS_PER_MODEL", "unlimited")
    ceiling = None if raw_ceiling == "unlimited" else int(raw_ceiling)
    packet_chars = _integer("COLLAB_PEER_PACKET_CHARS", 6000)
    return CollaborationEngineV2Agent(
        strategy=create_strategy(spec.strategy, packet_chars=packet_chars, models=MODELS),
        condition=spec.condition,
        max_calls_per_model=ceiling,
        generation_max_tokens=_integer("COLLAB_GENERATION_MAX_TOKENS", 12000),
        temperature=float(os.environ.get("COLLAB_TEMPERATURE", "0.2")),
        seed=_integer("COLLAB_SEED", 1),
        max_restarts=_integer("COLLAB_MAX_RESTARTS", 2),
        diagnostic_chars=_integer("COLLAB_DIAGNOSTIC_CHARS", 6000),
        failure_memory_chars=_integer("COLLAB_FAILURE_MEMORY_CHARS", 3000),
        peer_packet_chars=packet_chars,
        dispatch_cutoff_s=float(
            os.environ.get("COLLAB_DISPATCH_CUTOFF_S", str(max(1, time_limit - 720)))
        ),
        max_cost_free_429_retries=_integer("COLLAB_MAX_FREE_429_RETRIES", 2),
        enable_salvage=spec.salvage,
        salvage_check_timeout_s=_integer("COLLAB_SALVAGE_CHECK_TIMEOUT_S", 2),
        model_call_wall_timeout_s=float(
            os.environ.get("COLLAB_MODEL_CALL_WALL_TIMEOUT_S", "420")
        ),
        fast_track_reserved_calls=spec.fast_track_reserved_calls,
        reserve_release_margin_s=float(
            os.environ.get("COLLAB_RESERVE_RELEASE_MARGIN_S", "120")
        ),
    )


def create_c0_agent() -> CollaborationEngineV2Agent:
    return create_candidate("c0")


def create_c1_agent() -> CollaborationEngineV2Agent:
    return create_candidate("c1")


def create_c2_agent() -> CollaborationEngineV2Agent:
    return create_candidate("c2")


def create_c0plus_reserve_agent() -> CollaborationEngineV2Agent:
    return create_candidate("c0plus-reserve")


def create_c1plus_fill_reserve_agent() -> CollaborationEngineV2Agent:
    return create_candidate("c1plus-fill-reserve")


CANDIDATE_FACTORIES: dict[str, Callable[[], CollaborationEngineV2Agent]] = {
    "c0": create_c0_agent,
    "c1": create_c1_agent,
    "c2": create_c2_agent,
    "c0plus-reserve": create_c0plus_reserve_agent,
    "c1plus-fill-reserve": create_c1plus_fill_reserve_agent,
}
