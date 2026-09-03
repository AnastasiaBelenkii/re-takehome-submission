#!/usr/bin/env python3
"""Report counts of credential-shaped byte patterns without printing matches."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


PATTERNS = {
    "openai_style": re.compile(rb"sk-[A-Za-z0-9_-]{20,}"),
    "openrouter": re.compile(rb"sk-or-v1-[0-9a-fA-F]{32,}"),
    "aws_access": re.compile(rb"AKIA[0-9A-Z]{16}"),
    "digitalocean_pat": re.compile(rb"dop_v1_[0-9a-fA-F]{32,}"),
    "private_key": re.compile(rb"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
    "bearer_token": re.compile(
        rb"Authorization[^\r\n]{0,20}Bearer[ \t]+[A-Za-z0-9._~+/-]{20,}", re.I
    ),
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("roots", nargs="+", type=Path)
    args = parser.parse_args()
    missing = [str(root) for root in args.roots if not root.is_dir()]
    if missing:
        parser.error("archive root does not exist: " + ", ".join(missing))
    counts = {name: 0 for name in PATTERNS}
    files: dict[str, set[str]] = {name: set() for name in PATTERNS}
    for root in args.roots:
        for path in root.rglob("*"):
            if not path.is_file():
                continue
            try:
                with path.open("rb") as handle:
                    while chunk := handle.read(4 * 1024 * 1024):
                        for name, pattern in PATTERNS.items():
                            matches = len(pattern.findall(chunk))
                            counts[name] += matches
                            if matches:
                                files[name].add(f"{root.name}/{path.relative_to(root)}")
            except OSError:
                pass
    print(json.dumps({
        name: {"matches": counts[name], "files": len(files[name])}
        for name in PATTERNS
    }, sort_keys=True))
    return 1 if any(counts.values()) else 0


if __name__ == "__main__":
    raise SystemExit(main())
