"""Packet-only C0/C1/C2 strategies with no access to services or track state."""

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

    def after_round(self, observations: Sequence[TrackObservation]) -> Sequence[PeerPacket]: ...


def _excerpt(text: str, limit: int) -> str:
    text = text.strip()
    if len(text) <= limit:
        return text
    marker = "\n...[peer excerpt bounded]...\n"
    if limit <= len(marker):
        return text[:limit]
    available = limit - len(marker)
    head = (available * 2) // 3
    return text[:head] + marker + text[-(available - head):]


def _content(observation: TrackObservation, limit: int) -> str:
    header = "Independent peer's failed Lean candidate:\n"
    middle = "\n\nLean diagnostics from that candidate:\n"
    available = max(0, limit - len(header) - len(middle))
    candidate_limit = (available * 2) // 3
    return (
        header + _excerpt(observation.candidate, candidate_limit) + middle
        + _excerpt(observation.diagnostics, available - candidate_limit)
    )[:limit]


class NoCollaboration:
    strategy_id = "none"

    def after_round(self, observations: Sequence[TrackObservation]) -> tuple[()]:
        return ()


class ReciprocalCadence:
    """Exchange after the first (C1) or every (C2) complete dual failure."""

    def __init__(self, *, packet_chars: int, repeat: bool) -> None:
        self.packet_chars = packet_chars
        self.repeat = repeat
        self.exchanges = 0
        self.strategy_id = "reciprocal-every-eligible-v1" if repeat else "reciprocal-once-v1"

    def after_round(self, observations: Sequence[TrackObservation]) -> tuple[PeerPacket, ...]:
        if len(observations) != 2 or (self.exchanges and not self.repeat):
            return ()
        ordered = sorted(observations, key=lambda item: item.model)
        if ordered[0].round != ordered[1].round or any(item.accepted for item in ordered):
            return ()
        left, right = ordered
        self.exchanges += 1
        return (
            PeerPacket(left.model, right.model, _content(right, self.packet_chars), self.strategy_id),
            PeerPacket(right.model, left.model, _content(left, self.packet_chars), self.strategy_id),
        )


def create_strategy(strategy_id: str, *, packet_chars: int) -> CollaborationStrategy:
    factories = {
        "none": lambda: NoCollaboration(),
        "reciprocal-once-v1": lambda: ReciprocalCadence(packet_chars=packet_chars, repeat=False),
        "reciprocal-every-eligible-v1": lambda: ReciprocalCadence(packet_chars=packet_chars, repeat=True),
    }
    try:
        return factories[strategy_id]()
    except KeyError as exc:
        raise ValueError(f"unknown collaboration strategy: {strategy_id!r}") from exc

