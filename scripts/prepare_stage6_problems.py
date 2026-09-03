#!/usr/bin/env python3
"""Materialize the frozen miniF2F Stage 6 selection as experiment inputs."""

from __future__ import annotations

import argparse
import json
import re
import shutil
from pathlib import Path


def declaration_names(source: str, kind: str) -> list[str]:
    return re.findall(rf"(?m)^\s*{kind}\s+([A-Za-z_][A-Za-z0-9_'.]*)\b", source)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--selection", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    selection = json.loads(args.selection.read_text())
    survivors = selection["survivors"]
    if len(survivors) != 32:
        raise ValueError(f"expected 32 frozen survivors, found {len(survivors)}")
    manifest = {"schema_version": 1, "set": "stage6-expanded-minif2f-test", "problems": []}
    for record in survivors:
        problem = record["name"]
        source_path = args.source / record["path"]
        challenge = source_path.read_text()
        if challenge.splitlines()[0] != "import Mathlib":
            raise ValueError(f"noncanonical import header: {problem}")
        destination = args.output / problem
        destination.mkdir(parents=True, exist_ok=False)
        shutil.copy2(source_path, destination / "challenge.lean")
        (destination / "problem.md").write_text(
            f"# {problem}\n\nProve `{problem}` as formally stated in `challenge.lean`. "
            "This statement is from the miniF2F Lean 4 test split.\n"
        )
        manifest["problems"].append({
            "id": problem,
            "theorem_names": declaration_names(challenge, "theorem") + declaration_names(challenge, "lemma"),
            "definition_names": declaration_names(challenge, "def") + declaration_names(challenge, "abbrev"),
            "numeric_answer_names": [],
        })
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")


if __name__ == "__main__":
    main()
