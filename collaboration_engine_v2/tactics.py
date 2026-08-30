"""Deterministic, declaration-preserving call-zero tactic candidate."""

from __future__ import annotations

import re

TACTIC_CASCADE = "first | omega | norm_num | nlinarith | linarith | ring | aesop | simp_all"


def tactic_candidate(challenge: str) -> str | None:
    """Replace proof holes only; declaration text and numeric answers stay byte-identical."""
    candidate, count = re.subn(r"\bsorry\b", TACTIC_CASCADE, challenge)
    return candidate if count else None


def declaration_fingerprint(source: str) -> tuple[str, ...]:
    """Conservative normalized fingerprints for named declaration headers.

    This intentionally handles the challenge corpus' declarations rather than
    pretending to be a Lean parser. Final authority remains Comparator.
    """
    starts = list(re.finditer(
        r"(?m)^\s*(?:theorem|lemma|def|abbrev|opaque)\s+[A-Za-z_][A-Za-z0-9_'.]*\b",
        source,
    ))
    answer: list[str] = []
    for index, match in enumerate(starts):
        end = starts[index + 1].start() if index + 1 < len(starts) else len(source)
        block = source[match.start():end]
        header, separator, _body = block.partition(":=")
        if not separator:
            header = block.partition(" where")[0]
        answer.append(" ".join(header.split()))
    return tuple(answer)


def declarations_unchanged(challenge: str, candidate: str) -> bool:
    return declaration_fingerprint(challenge) == declaration_fingerprint(candidate)

