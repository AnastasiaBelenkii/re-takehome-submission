#!/usr/bin/env python3
"""Validate one collected uplift pilot bundle and preserve the verdict."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
for import_root in (ROOT / "src", ROOT):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from uplift_pilot.validation import append_ledger, validate_bundle, write_validation_artifacts


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundle", type=Path)
    parser.add_argument("--condition", type=Path, required=True)
    parser.add_argument("--commit", required=True, help="expected full 40-character commit SHA")
    parser.add_argument("--ledger", type=Path, help="append the compact result to this JSONL ledger")
    args = parser.parse_args(argv)
    validation = validate_bundle(
        args.bundle, expected_condition_path=args.condition, expected_commit=args.commit
    )
    write_validation_artifacts(args.bundle, validation)
    if args.ledger:
        provenance_path = args.bundle / "provenance.json"
        try:
            provenance = json.loads(provenance_path.read_text(encoding="utf-8"))
            append_ledger(args.ledger, validation, provenance)
        except (OSError, json.JSONDecodeError, ValueError) as exc:
            print(f"ledger append failed: {exc}", file=sys.stderr)
            return 2
    print(json.dumps(validation.report, sort_keys=True, separators=(",", ":")))
    print(validation.table, file=sys.stderr, end="")
    if validation.errors:
        print("validation reasons:", file=sys.stderr)
        for error in validation.errors:
            print(f"- {error}", file=sys.stderr)
    return 0 if validation.valid else 1


if __name__ == "__main__":
    raise SystemExit(main())
