#!/usr/bin/env python3
"""Index a staged Git mirror of evaluator endpoint artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path


NAMES = {"result.json", "events.jsonl", "provenance.json", "preliminary-status.json"}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    archives = root / "archives"
    if not archives.is_dir():
        parser.error(f"missing archives directory under {root}")

    rows = []
    unique: dict[str, dict[str, int]] = defaultdict(dict)
    for path in sorted(archives.rglob("*")):
        if not path.is_file() or path.name not in NAMES:
            continue
        digest = sha256_file(path)
        size = path.stat().st_size
        relative = path.relative_to(root).as_posix()
        rows.append({"git_path": f"evidence/{relative}", "sha256": digest, "size_bytes": size})
        unique[path.name].setdefault(digest, size)

    counts = {}
    for name in sorted(NAMES):
        named_rows = [row for row in rows if Path(str(row["git_path"])).name == name]
        counts[name] = {
            "path_count": len(named_rows),
            "path_bytes": sum(int(row["size_bytes"]) for row in named_rows),
            "unique_blob_count": len(unique[name]),
            "unique_blob_bytes": sum(unique[name].values()),
        }
    (root / "ENDPOINT_INDEX.json").write_text(
        json.dumps(
            {"schema_version": 1, "counts": counts, "files": rows},
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
    (root / "README.md").write_text(
        "# Evaluator endpoint evidence\n\n"
        "This branch preserves every archived `result.json`, `events.jsonl`, "
        "`provenance.json`, and `preliminary-status.json` at its original path "
        "beneath an archive namespace. These files supply Lean and Comparator "
        "outcomes that are not present in call transcripts.\n\n"
        "- `archives/legacy-20260901/` is the September 1 consolidated snapshot.\n"
        "- `archives/matched-stage3-20260902/` is the September 2 matched Stage 3 supplement.\n"
        "- `ENDPOINT_INDEX.json` records every Git path, byte size, and SHA-256.\n\n"
        "Duplicate archive mirrors retain distinct paths but share identical Git "
        "blob objects. No artifact has been transformed.\n"
    )
    print(json.dumps({"file_count": len(rows), "counts": counts}, sort_keys=True))


if __name__ == "__main__":
    main()
