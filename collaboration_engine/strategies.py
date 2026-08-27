"""Constrained information-sharing policies.

Strategies receive immutable observations and may only return bounded packets for
the *next already-scheduled* model call.  They never receive Services, prompts, or
mutable solver state, so they cannot change budgets, retries, Lean checks, or the
H+D state machine.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol, Sequence


@dataclass(frozen=True)
class TrackObservation:
    model: str
    round: int
    call: int
    candidate: str
    diagnostics: str
    accepted: bool
    timed_out: bool


@dataclass(frozen=True)
class PeerPacket:
    target_model: str
    source_model: str
    content: str
    kind: str


class CollaborationStrategy(Protocol):
    strategy_id: str

    def after_round(
        self, observations: Sequence[TrackObservation]
    ) -> Sequence[PeerPacket]: ...


class NoCollaboration:
    strategy_id = "none"

    def after_round(self, observations: Sequence[TrackObservation]) -> tuple[()]:
        return ()


def _bounded_peer_content(observation: TrackObservation, limit: int) -> str:
    header = "Independent peer's failed Lean candidate:\n"
    middle = "\n\nLean diagnostics from that candidate:\n"
    available = max(0, limit - len(header) - len(middle))
    candidate_limit = (available * 2) // 3
    diagnostic_limit = available - candidate_limit
    candidate = _excerpt(observation.candidate, candidate_limit)
    diagnostics = _excerpt(observation.diagnostics, diagnostic_limit)
    return f"{header}{candidate}{middle}{diagnostics}"[:limit]


def _excerpt(text: str, limit: int) -> str:
    text = text.strip()
    if len(text) <= limit:
        return text
    marker = "\n...[peer excerpt bounded]...\n"
    if limit <= len(marker):
        return text[:limit]
    available = limit - len(marker)
    head = (available * 2) // 3
    return text[:head] + marker + text[-(available - head) :]


class ReciprocalCrossRepair:
    """One symmetric exchange after both first-round candidates fail."""

    strategy_id = "reciprocal-cross-repair-v1"

    def __init__(self, *, packet_chars: int) -> None:
        self.packet_chars = packet_chars

    def after_round(
        self, observations: Sequence[TrackObservation]
    ) -> tuple[PeerPacket, ...]:
        if len(observations) != 2:
            return ()
        ordered = sorted(observations, key=lambda item: item.model)
        if any(item.round != 1 or item.accepted for item in ordered):
            return ()
        left, right = ordered
        return (
            PeerPacket(
                target_model=left.model,
                source_model=right.model,
                content=_bounded_peer_content(right, self.packet_chars),
                kind=self.strategy_id,
            ),
            PeerPacket(
                target_model=right.model,
                source_model=left.model,
                content=_bounded_peer_content(left, self.packet_chars),
                kind=self.strategy_id,
            ),
        )


def create_strategy(strategy_id: str, *, packet_chars: int) -> CollaborationStrategy:
    factories = {
        "none": lambda: NoCollaboration(),
        "reciprocal-cross-repair-v1": lambda: ReciprocalCrossRepair(
            packet_chars=packet_chars
        ),
    }
    try:
        return factories[strategy_id]()
    except KeyError as exc:
        raise ValueError(f"unknown collaboration strategy: {strategy_id!r}") from exc
