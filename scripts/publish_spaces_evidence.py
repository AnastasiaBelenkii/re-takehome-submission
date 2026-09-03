#!/usr/bin/env python3
"""Upload an evidence tree to DigitalOcean Spaces with resumable verification."""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import mimetypes
from pathlib import Path
from typing import Any
from urllib.parse import quote
from urllib.request import urlopen

import boto3
from boto3.s3.transfer import TransferConfig
from botocore.exceptions import ClientError


def load_credentials(path: Path) -> dict[str, str]:
    values: dict[str, str] = {}
    for raw in path.read_text().splitlines():
        if raw and not raw.lstrip().startswith("#") and "=" in raw:
            key, value = raw.split("=", 1)
            values[key.strip()] = value.strip()
    required = {
        "SPACES_BUCKET", "SPACES_REGION", "SPACES_ENDPOINT",
        "SPACES_ACCESS_KEY_ID", "SPACES_SECRET_ACCESS_KEY",
    }
    missing = sorted(required - values.keys())
    if missing:
        raise RuntimeError(f"credential file lacks fields: {', '.join(missing)}")
    return values


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def public_url(values: dict[str, str], key: str) -> str:
    encoded = "/".join(quote(part, safe="-._~") for part in key.split("/"))
    return (
        f"https://{values['SPACES_BUCKET']}.{values['SPACES_REGION']}"
        f".digitaloceanspaces.com/{encoded}"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--credentials", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--prefix", default="")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--progress-every", type=int, default=1)
    parser.add_argument("--verify-content", action="store_true")
    parser.add_argument("--results", type=Path, required=True)
    args = parser.parse_args()
    if args.workers < 1 or args.progress_every < 1:
        parser.error("--workers and --progress-every must be positive")

    values = load_credentials(args.credentials)
    source = args.source.resolve()
    if not source.is_dir():
        parser.error(f"source directory does not exist: {source}")
    args.results.parent.mkdir(parents=True, exist_ok=True)
    client = boto3.client(
        "s3",
        region_name=values["SPACES_REGION"],
        endpoint_url=values["SPACES_ENDPOINT"],
        aws_access_key_id=values["SPACES_ACCESS_KEY_ID"],
        aws_secret_access_key=values["SPACES_SECRET_ACCESS_KEY"],
    )
    transfer = TransferConfig(
        multipart_threshold=64 * 1024 * 1024,
        multipart_chunksize=32 * 1024 * 1024,
        max_concurrency=2,
        use_threads=True,
    )
    prefix = args.prefix.strip("/")
    files = sorted(path for path in source.rglob("*") if path.is_file())

    def upload(path: Path) -> dict[str, Any]:
        relative = path.relative_to(source).as_posix()
        key = "/".join(part for part in (prefix, relative) if part)
        digest = sha256_file(path)
        size = path.stat().st_size
        skipped = False
        try:
            head = client.head_object(Bucket=values["SPACES_BUCKET"], Key=key)
            skipped = (
                int(head.get("ContentLength", -1)) == size
                and (head.get("Metadata") or {}).get("sha256") == digest
            )
        except ClientError as exc:
            status = exc.response.get("ResponseMetadata", {}).get("HTTPStatusCode")
            if status != 404:
                raise
        if not skipped:
            content_type = mimetypes.guess_type(path.name)[0] or "application/octet-stream"
            client.upload_file(
                str(path), values["SPACES_BUCKET"], key,
                ExtraArgs={
                    "ACL": "public-read",
                    "ContentType": content_type,
                    "Metadata": {"sha256": digest},
                },
                Config=transfer,
            )
        else:
            client.put_object_acl(
                Bucket=values["SPACES_BUCKET"], Key=key, ACL="public-read"
            )
        verified = None
        if args.verify_content:
            remote = hashlib.sha256()
            with urlopen(public_url(values, key), timeout=120) as response:
                while chunk := response.read(1024 * 1024):
                    remote.update(chunk)
            verified = remote.hexdigest() == digest
            if not verified:
                raise RuntimeError(f"content verification failed for {key}")
        return {
            "key": key,
            "source": str(path),
            "size_bytes": size,
            "sha256": digest,
            "public_url": public_url(values, key),
            "skipped_existing": skipped,
            "content_verified": verified,
        }

    rows: list[dict[str, Any]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(upload, path): path for path in files}
        for number, future in enumerate(concurrent.futures.as_completed(futures), 1):
            row = future.result()
            rows.append(row)
            if number == len(files) or number % args.progress_every == 0:
                print(json.dumps({
                    "completed": number,
                    "total": len(files),
                    "key": row["key"],
                    "size_bytes": row["size_bytes"],
                    "verified": row["content_verified"],
                }), flush=True)
    rows.sort(key=lambda row: row["key"])
    args.results.write_text(json.dumps(rows, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "uploaded_objects": len(rows),
        "uploaded_bytes": sum(row["size_bytes"] for row in rows),
        "all_content_verified": all(row["content_verified"] is not False for row in rows),
    }))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
