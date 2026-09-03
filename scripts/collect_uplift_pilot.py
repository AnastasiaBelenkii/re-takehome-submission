#!/usr/bin/env python3
"""Collect an immutable self-contained run bundle with rsync --partial."""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path


def _bundle_name(source: str) -> str:
    value = source.rstrip("/")
    tail = value.rsplit(":", 1)[-1].rsplit("/", 1)[-1]
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{1,199}", tail):
        raise ValueError(f"cannot derive a safe bundle name from {source!r}")
    return tail


def collect(source: str, archive_root: Path) -> Path:
    if shutil.which("rsync") is None:
        raise RuntimeError("rsync is required")
    name = _bundle_name(source)
    archive_root = archive_root.resolve()
    destination = archive_root / name
    staging = archive_root / f".{name}.partial"
    if destination.exists():
        raise FileExistsError(f"refusing to reuse collected bundle: {destination}")
    archive_root.mkdir(parents=True, exist_ok=True)
    if staging.exists() and not staging.is_dir():
        raise FileExistsError(f"collection staging path is not a directory: {staging}")
    staging.mkdir(exist_ok=True)
    subprocess.run(
        [
            "rsync",
            "--archive",
            "--partial",
            "--protect-args",
            source.rstrip("/") + "/",
            str(staging) + "/",
        ],
        check=True,
    )
    # Publication is atomic. An interrupted transfer leaves only the hidden
    # staging directory, which a later invocation can safely resume with rsync.
    staging.rename(destination)
    return destination


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", help="worker:/absolute/run-bundle or a local bundle path")
    parser.add_argument("archive_root", type=Path)
    args = parser.parse_args(argv)
    try:
        destination = collect(args.source, args.archive_root)
    except (RuntimeError, ValueError, FileExistsError, subprocess.CalledProcessError) as exc:
        print(f"collection failed: {exc}", file=sys.stderr)
        return 1
    print(destination)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
