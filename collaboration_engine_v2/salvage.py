"""Conservative, Lean-validated partial-proof salvage.

This module only proposes source transformations.  The warm Lean service is
always the authority on whether a proposed skeleton compiles up to explicit
``sorry`` holes.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any, Sequence


_DECLARATION = re.compile(
    r"^(?:theorem|lemma|def|abbrev|opaque)\s+[A-Za-z_][A-Za-z0-9_'.]*\b"
)
_SORRY = re.compile(r"\bsorry\b")


@dataclass(frozen=True)
class SorrificationCandidate:
    source: str
    mode: str
    declaration_line: int
    error_line: int
    retained_lines: int
    residual_goals: str


def contains_sorry(source: str) -> bool:
    return bool(_SORRY.search(source))


def error_messages(messages: Sequence[dict[str, Any]]) -> list[dict[str, Any]]:
    return [message for message in messages if message.get("severity") == "error"]


def residual_goal_text(messages: Sequence[dict[str, Any]], *, limit: int = 6000) -> str:
    chunks: list[str] = []
    for message in error_messages(messages):
        data = str(message.get("data", "")).strip()
        if data and data not in chunks:
            chunks.append(data)
    text = "\n\n--- residual diagnostic ---\n\n".join(chunks)
    if len(text) > limit:
        text = text[: max(0, limit - 32)] + "\n...[residual goals bounded]"
    return text


def _position_line(message: dict[str, Any]) -> int | None:
    position = message.get("pos")
    if not isinstance(position, dict):
        return None
    line = position.get("line")
    if isinstance(line, bool) or not isinstance(line, int) or line < 1:
        return None
    return line


def _position_end_line(message: dict[str, Any]) -> int | None:
    position = message.get("endPos")
    if not isinstance(position, dict):
        return None
    line = position.get("line")
    if isinstance(line, bool) or not isinstance(line, int) or line < 1:
        return None
    return line


def _declaration_bounds(lines: list[str], error_index: int) -> tuple[int, int] | None:
    starts = [
        index for index, line in enumerate(lines)
        if line == line.lstrip() and _DECLARATION.match(line)
    ]
    eligible = [index for index in starts if index <= error_index]
    if not eligible:
        return None
    start = eligible[-1]
    later = [index for index in starts if index > start]
    return start, (later[0] if later else len(lines))


def _proof_body_line(lines: list[str], start: int, end: int) -> int | None:
    for index in range(start, end):
        if ":= by" in lines[index] or lines[index].rstrip().endswith(" where"):
            return index
    return None


def _body_indent(lines: list[str], body_line: int, end: int) -> str:
    for index in range(body_line + 1, end):
        if lines[index].strip():
            indent = lines[index][: len(lines[index]) - len(lines[index].lstrip())]
            if indent:
                return indent
    return "  "


def _render(lines: list[str], *, keep_through: int, end: int, indent: str) -> str:
    answer = lines[: keep_through + 1] + [indent + "all_goals sorry"] + lines[end:]
    return "\n".join(answer).rstrip() + "\n"


def _render_span(lines: list[str], *, start: int, stop: int) -> str:
    indent = lines[start][: len(lines[start]) - len(lines[start].lstrip())]
    answer = lines[:start] + [indent + "sorry"] + lines[stop + 1:]
    return "\n".join(answer).rstrip() + "\n"


def propose_sorrifications(
    source: str,
    messages: Sequence[dict[str, Any]],
    *,
    residual_chars: int = 6000,
) -> tuple[SorrificationCandidate, ...]:
    """Propose progressively wider, compiler-positioned skeletons.

    The first replaces only the reported failing line span.  The second drops
    the failing suffix while preserving its proof prefix.  A final whole-body
    proposal is returned for offline measurement, but live salvage rejects any
    proposal with zero retained proof lines.  All preserve later top-level
    declarations byte-for-byte modulo the final newline.  Candidates are not
    trusted until warm Lean validates them.
    """

    if contains_sorry(source):
        return ()
    errors = error_messages(messages)
    positioned = [line for line in (_position_line(item) for item in errors) if line]
    if not positioned:
        return ()
    lines = source.replace("\r\n", "\n").splitlines()
    error_index = min(positioned) - 1
    if not 0 <= error_index < len(lines):
        return ()
    bounds = _declaration_bounds(lines, error_index)
    if bounds is None:
        return ()
    start, end = bounds
    body_line = _proof_body_line(lines, start, end)
    if body_line is None or error_index <= body_line:
        return ()
    indent = _body_indent(lines, body_line, end)
    residual = residual_goal_text(errors, limit=residual_chars)
    answer: list[SorrificationCandidate] = []

    earliest = min(errors, key=lambda item: _position_line(item) or 10**9)
    end_line = _position_end_line(earliest) or (error_index + 1)
    span_end = min(end - 1, max(error_index, end_line - 1))
    if error_index > body_line:
        span = SorrificationCandidate(
            source=_render_span(lines, start=error_index, stop=span_end),
            mode="diagnostic_span",
            declaration_line=start + 1,
            error_line=error_index + 1,
            retained_lines=max(0, (end - body_line - 1) - (span_end - error_index + 1)),
            residual_goals=residual,
        )
        if span.retained_lines > 0:
            answer.append(span)

    prefix_keep = max(body_line, error_index - 1)
    if prefix_keep > body_line:
        suffix = SorrificationCandidate(
            source=_render(lines, keep_through=prefix_keep, end=end, indent=indent),
            mode="failing_suffix",
            declaration_line=start + 1,
            error_line=error_index + 1,
            retained_lines=prefix_keep - body_line,
            residual_goals=residual,
        )
        if not answer or suffix.source != answer[-1].source:
            answer.append(suffix)

    whole = SorrificationCandidate(
        source=_render(lines, keep_through=body_line, end=end, indent=indent),
        mode="whole_proof_body",
        declaration_line=start + 1,
        error_line=error_index + 1,
        retained_lines=0,
        residual_goals=residual,
    )
    if not answer or whole.source != answer[-1].source:
        answer.append(whole)
    return tuple(answer[:3])


def compiles_with_sorry(source: str, check: Any) -> bool:
    return (
        contains_sorry(source)
        and not bool(getattr(check, "timed_out", False))
        and not any(
            message.get("severity") == "error"
            for message in getattr(check, "messages", [])
        )
    )
