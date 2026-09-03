#!/usr/bin/env python3
"""Build a content-addressed, Git-friendly archive of raw transcripts."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path


def parse_archive(value: str) -> tuple[str, Path]:
    try:
        archive_id, root = value.split("=", 1)
    except ValueError as exc:
        raise argparse.ArgumentTypeError("archive must be ARCHIVE_ID=LOCAL_ROOT") from exc
    path = Path(root).resolve()
    if not path.is_dir():
        raise argparse.ArgumentTypeError(f"archive root is not a directory: {path}")
    return archive_id, path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--archive", action="append", required=True, type=parse_archive)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()

    transcripts_dir = args.output / "transcripts"
    transcripts_dir.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, object]] = []
    unique: dict[str, Path] = {}
    for archive_id, root in args.archive:
        for path in sorted(root.rglob("transcript.json")):
            payload = path.read_bytes()
            digest = hashlib.sha256(payload).hexdigest()
            unique.setdefault(digest, path)
            rows.append(
                {
                    "archive_id": archive_id,
                    "archive_relative_path": path.relative_to(root).as_posix(),
                    "git_path": f"evidence/transcripts/{digest}.json",
                    "sha256": digest,
                    "size_bytes": len(payload),
                }
            )
    for digest, source in sorted(unique.items()):
        shutil.copyfile(source, transcripts_dir / f"{digest}.json")
    rows.sort(key=lambda row: (str(row["archive_id"]), str(row["archive_relative_path"])))
    (args.output / "TRANSCRIPT_INDEX.json").write_text(
        json.dumps(
            {
                "schema_version": 1,
                "path_count": len(rows),
                "unique_transcript_count": len(unique),
                "transcripts": rows,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
    (args.output / "README.md").write_text(
        "# Complete archived transcript mirror\n\n"
        f"This branch contains {len(unique)} unique raw transcript JSON payloads "
        f"covering {len(rows)} original archive paths. Files are named by SHA-256; "
        "`TRANSCRIPT_INDEX.json` maps every source path to its Git blob.\n\n"
        "This convenience branch includes historical transcripts that lack exact "
        "commit provenance. Use the per-commit `evidence/run-data-*` branches when "
        "an exact generating-code relationship is required.\n"
    )
    print(json.dumps({"path_count": len(rows), "unique_transcript_count": len(unique)}))


if __name__ == "__main__":
    main()
