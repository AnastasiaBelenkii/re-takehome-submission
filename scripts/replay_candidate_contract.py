#!/usr/bin/env python3
"""Replay recorded model outputs through old and current candidate contracts.

This is a deterministic stage-0 diagnostic. It classifies already-generated
outputs; it cannot predict the responses that transactional state would have
caused models to generate later in the trajectory.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from baselines.simple_agent import _extract_lean
from collaboration_engine_v2.tactics import (
    canonicalize_imports,
    declaration_fingerprint,
    declarations_unchanged,
    imports_unchanged,
    required_declarations_present,
)


def _challenge(transcript: dict) -> str:
    for call in transcript.get("calls", []):
        for message in call.get("request", {}).get("messages", []):
            if message.get("role") != "user":
                continue
            fenced = re.findall(
                r"```(?:lean|lean4)?\s*\n(.*?)```",
                str(message.get("content", "")),
                flags=re.DOTALL | re.IGNORECASE,
            )
            if fenced and "Pristine Lean challenge:" in str(message.get("content", "")):
                return fenced[-1]
    raise ValueError("transcript has no pristine Lean challenge block")


def classify(path: Path) -> dict:
    transcript = json.loads(path.read_text(encoding="utf-8"))
    challenge = _challenge(transcript)
    required_count = len(declaration_fingerprint(challenge))
    current = challenge
    counts = {
        "calls": len(transcript.get("calls", [])),
        "outputs_with_text": 0,
        "old_gate_rejected": 0,
        "new_declaration_gate_rejected": 0,
        "new_import_gate_rejected": 0,
        "new_contract_rejected": 0,
        "structural_gate_rejected": 0,
        "released_by_structural_gate": 0,
        "newly_admitted": 0,
        "newly_admitted_with_extra_declarations": 0,
    }
    for call in transcript.get("calls", []):
        try:
            content = call["response"]["choices"][0]["message"]["content"]
        except (KeyError, IndexError, TypeError):
            continue
        if not isinstance(content, str) or not content:
            continue
        counts["outputs_with_text"] += 1
        extracted = _extract_lean(content, fallback=current)
        current = extracted
        old_ok = declaration_fingerprint(challenge) == declaration_fingerprint(extracted)
        imports_ok = imports_unchanged(challenge, extracted)
        proposal = canonicalize_imports(extracted)
        declarations_ok = declarations_unchanged(challenge, proposal)
        structural_ok = required_declarations_present(challenge, proposal)
        contract_ok = declarations_ok
        counts["old_gate_rejected"] += int(not old_ok)
        counts["new_declaration_gate_rejected"] += int(not declarations_ok)
        counts["new_import_gate_rejected"] += int(not imports_ok)
        counts["new_contract_rejected"] += int(not contract_ok)
        counts["structural_gate_rejected"] += int(not structural_ok)
        counts["released_by_structural_gate"] += int(not contract_ok and structural_ok)
        counts["newly_admitted"] += int(not old_ok and contract_ok)
        counts["newly_admitted_with_extra_declarations"] += int(
            not old_ok
            and contract_ok
            and len(declaration_fingerprint(proposal)) > required_count
        )
    return {
        "path": str(path.resolve()),
        "problem_id": transcript.get("problem_id"),
        **counts,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("transcripts", nargs="+", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rows = [classify(path) for path in args.transcripts]
    totals = {
        key: sum(int(row[key]) for row in rows)
        for key in (
            "calls", "outputs_with_text", "old_gate_rejected",
            "new_declaration_gate_rejected", "new_import_gate_rejected",
            "new_contract_rejected", "newly_admitted",
            "newly_admitted_with_extra_declarations", "structural_gate_rejected",
            "released_by_structural_gate",
        )
    }
    result = {
        "schema_version": 1,
        "method": (
            "Recorded outputs re-extracted in original order and classified by old "
            "whole-list equality versus the current required-declaration contract after "
            "deterministic import canonicalization, plus the proposed live structural "
            "name-and-kind completeness guard. The import count records how often "
            "canonicalization changes the original response. "
            "This is not a counterfactual model trajectory."
        ),
        "rows": rows,
        "totals": totals,
    }
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
