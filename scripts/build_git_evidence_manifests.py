#!/usr/bin/env python3
"""Build small Git manifests linking code commits to public run artifacts.

The manifests contain pointers and checksums, never the (large) artifacts
themselves.  A caller can commit each generated directory directly on top of
the generating commit to make the code-to-evidence relationship explicit in
Git history.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from collections import defaultdict
from pathlib import Path
from urllib.parse import quote


def parse_archive(value: str) -> tuple[str, Path, str]:
    try:
        archive_id, root, raw_prefix = value.split("=", 2)
    except ValueError as exc:
        raise argparse.ArgumentTypeError(
            "archive must be ARCHIVE_ID=LOCAL_ROOT=PUBLIC_RAW_PREFIX"
        ) from exc
    path = Path(root).resolve()
    if not path.is_dir():
        raise argparse.ArgumentTypeError(f"archive root is not a directory: {path}")
    return archive_id, path, raw_prefix.strip("/")


def public_url(base: str, *parts: str) -> str:
    path = "/".join(quote(part.strip("/"), safe="/-._~") for part in parts)
    return f"{base.rstrip('/')}/{path}"


def stable_hash(value: object) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--archive", action="append", required=True, type=parse_archive)
    parser.add_argument("--public-base-url", required=True)
    parser.add_argument("--catalog-url", required=True)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument(
        "--include-transcripts",
        action="store_true",
        help="copy associated transcript.json payloads into each commit directory",
    )
    args = parser.parse_args()

    by_commit: dict[str, list[dict[str, object]]] = defaultdict(list)
    transcript_sources: dict[str, dict[str, Path]] = defaultdict(dict)
    transcript_rows: dict[str, list[dict[str, object]]] = defaultdict(list)
    for archive_id, root, raw_prefix in args.archive:
        for provenance_path in sorted(root.rglob("provenance.json")):
            provenance_bytes = provenance_path.read_bytes()
            provenance = json.loads(provenance_bytes)
            commit = provenance.get("git_commit")
            if not isinstance(commit, str) or len(commit) != 40:
                raise ValueError(f"missing full git_commit in {provenance_path}")
            relative_path = provenance_path.relative_to(root).as_posix()
            run_path = provenance_path.parent.relative_to(root).as_posix()
            task = provenance.get("task") or {}
            by_commit[commit].append(
                {
                    "archive_id": archive_id,
                    "archive_relative_provenance_path": relative_path,
                    "condition": task.get("condition"),
                    "experiment": provenance.get("experiment"),
                    "problem": task.get("problem"),
                    "provenance_sha256": hashlib.sha256(provenance_bytes).hexdigest(),
                    "public_provenance_url": public_url(
                        args.public_base_url, raw_prefix, relative_path
                    ),
                    "public_run_prefix": public_url(
                        args.public_base_url, raw_prefix, run_path
                    )
                    + "/",
                    "seed": task.get("seed"),
                    "source_worker": provenance.get("worker"),
                    "task_id": task.get("task_id"),
                }
            )
            if args.include_transcripts:
                for transcript_path in sorted(provenance_path.parent.rglob("transcript.json")):
                    transcript_bytes = transcript_path.read_bytes()
                    transcript_sha = hashlib.sha256(transcript_bytes).hexdigest()
                    transcript_relative_path = transcript_path.relative_to(root).as_posix()
                    transcript_sources[commit][transcript_sha] = transcript_path
                    transcript_rows[commit].append(
                        {
                            "archive_id": archive_id,
                            "archive_relative_path": transcript_relative_path,
                            "git_path": f"evidence/transcripts/{transcript_sha}.json",
                            "public_raw_url": public_url(
                                args.public_base_url, raw_prefix, transcript_relative_path
                            ),
                            "sha256": transcript_sha,
                            "size_bytes": len(transcript_bytes),
                        }
                    )

    args.output.mkdir(parents=True, exist_ok=True)
    summary = []
    for commit, runs in sorted(by_commit.items()):
        runs.sort(key=lambda row: (str(row["archive_id"]), str(row["archive_relative_provenance_path"])))
        manifest = {
            "schema_version": 1,
            "generating_git_commit": commit,
            "relationship": "This evidence commit is a direct child of generating_git_commit.",
            "artifact_storage": "Public-read DigitalOcean Spaces objects; no artifacts were moved or rewritten.",
            "catalog_url": args.catalog_url,
            "run_count": len(runs),
            "runs_sha256": stable_hash(runs),
            "runs": runs,
        }
        target = args.output / commit
        target.mkdir(parents=True, exist_ok=True)
        manifest_path = target / "ARCHIVE_POINTER.json"
        manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        unique_transcript_count = 0
        if args.include_transcripts:
            transcripts_dir = target / "transcripts"
            transcripts_dir.mkdir(exist_ok=True)
            for transcript_sha, source in sorted(transcript_sources[commit].items()):
                shutil.copyfile(source, transcripts_dir / f"{transcript_sha}.json")
            rows = sorted(
                transcript_rows[commit],
                key=lambda row: (str(row["archive_id"]), str(row["archive_relative_path"])),
            )
            (target / "TRANSCRIPT_INDEX.json").write_text(
                json.dumps(
                    {
                        "schema_version": 1,
                        "generating_git_commit": commit,
                        "path_count": len(rows),
                        "unique_transcript_count": len(transcript_sources[commit]),
                        "transcripts": rows,
                    },
                    indent=2,
                    sort_keys=True,
                )
                + "\n"
            )
            unique_transcript_count = len(transcript_sources[commit])
        (target / "README.md").write_text(
            "# Archived run evidence\n\n"
            f"This Git commit is a direct child of generating code commit `{commit}`. "
            f"It links {len(runs)} archived run provenance record(s) to immutable, "
            "public-read object URLs. Large result and transcript artifacts remain in "
            "object storage rather than Git.\n\n"
            f"Queryable catalog: <{args.catalog_url}>\n\n"
            "See `ARCHIVE_POINTER.json` for per-run provenance URLs, source workers, "
            "conditions, problems, and SHA-256 checksums.\n"
            + (
                f"\nThis commit also contains {unique_transcript_count} unique raw "
                "transcript JSON payload(s) under `evidence/transcripts/`; "
                "`evidence/TRANSCRIPT_INDEX.json` maps their original archive paths.\n"
                if args.include_transcripts
                else ""
            )
        )
        summary.append(
            {
                "git_commit": commit,
                "run_count": len(runs),
                "unique_transcript_count": unique_transcript_count,
                "manifest_sha256": hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
            }
        )
    (args.output / "SUMMARY.json").write_text(
        json.dumps({"schema_version": 1, "commits": summary}, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps({"commit_count": len(summary), "run_count": sum(x["run_count"] for x in summary)}))


if __name__ == "__main__":
    main()
