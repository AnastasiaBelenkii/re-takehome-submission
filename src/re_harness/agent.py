"""Applicant-facing agent protocol."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Mapping, Protocol, runtime_checkable

if False:  # pragma: no cover - imports for type checkers without cycles
    from .lean import LeanClient
    from .llm import LLMClient

JSONValue = None | bool | int | float | str | list["JSONValue"] | dict[str, "JSONValue"]


@dataclass(frozen=True)
class Problem:
    id: str
    description: str
    challenge: str
    metadata: Mapping[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class AgentResult:
    solution: str
    metadata: Mapping[str, JSONValue] = field(default_factory=dict)


class Services:
    """Capabilities provided to an applicant agent for one problem."""

    def __init__(self, *, llm: "LLMClient", lean: "LeanClient", checkpoint, verify=None):
        self.llm = llm
        self.lean = lean
        self._checkpoint = checkpoint
        self._verify = verify

    def checkpoint(
        self, source: str, metadata: Mapping[str, JSONValue] | None = None
    ) -> None:
        """Atomically preserve a candidate for timeout/crash recovery."""

        self._checkpoint(source, dict(metadata or {}))

    async def verify(self, source: str) -> Mapping[str, JSONValue]:
        """Check a promising candidate under fresh holdout-style judging.

        This is intentionally separate from the warm Lean REPL. Agents should
        call it sparingly, normally only after a candidate passes warm Lean.
        """
        if self._verify is None:
            raise RuntimeError("fresh candidate verification is unavailable")
        result = self._verify(source)
        if hasattr(result, "__await__"):
            result = await result
        return result


@runtime_checkable
class Agent(Protocol):
    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        """Return the best complete Lean source for ``problem``."""
