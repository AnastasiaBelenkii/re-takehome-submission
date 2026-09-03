#!/usr/bin/env python3
"""Convert evidence JSONL tables to versioned Zstandard-compressed Parquet."""

from __future__ import annotations

import argparse
from pathlib import Path

import duckdb


def sql_path(path: Path) -> str:
    return str(path).replace("'", "''")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jsonl-dir", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    connection = duckdb.connect()
    for source in sorted(args.jsonl_dir.glob("*.jsonl")):
        destination = args.out / f"{source.stem}.parquet"
        if source.stat().st_size == 0:
            if source.stem != "conversion_errors":
                raise RuntimeError(f"unexpected empty table: {source}")
            query = (
                "SELECT CAST(NULL AS VARCHAR) AS archive_id, "
                "CAST(NULL AS VARCHAR) AS source_relative_path, "
                "CAST(NULL AS VARCHAR) AS error WHERE false"
            )
        else:
            query = (
                f"SELECT * FROM read_json_auto('{sql_path(source)}', "
                "format='newline_delimited', sample_size=-1, "
                "maximum_object_size=1073741824)"
            )
        connection.execute(
            f"COPY ({query}) TO '{sql_path(destination)}' "
            "(FORMAT PARQUET, COMPRESSION ZSTD)"
        )
        count = connection.execute(
            f"SELECT count(*) FROM read_parquet('{sql_path(destination)}')"
        ).fetchone()[0]
        print(f"{source.stem}\t{count}\t{destination.stat().st_size}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
