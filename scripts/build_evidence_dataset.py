#!/usr/bin/env python3
"""Build non-destructive analysis tables and transcript views from archives."""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import mimetypes
import os
from pathlib import Path
from typing import Any, Iterable
from urllib.parse import quote


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def dump_jsonl(path: Path, rows: Iterable[dict[str, Any]]) -> int:
    count = 0
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")
            count += 1
    return count


def source_host(relative: Path) -> str | None:
    parts = relative.parts
    return parts[1] if len(parts) > 1 and parts[0] == "hosts" else None


def task_name(relative: Path) -> str | None:
    parts = relative.parts
    try:
        return parts[parts.index("tasks") + 1]
    except (ValueError, IndexError):
        return None


def raw_url(base_url: str, archive_id: str, relative: Path) -> str:
    encoded = "/".join(quote(part, safe="-._~") for part in relative.parts)
    return f"{base_url}/raw/extracted/{quote(archive_id, safe='-._~')}/{encoded}"


def load_json(path: Path) -> Any:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def scalar(value: Any) -> Any:
    return value if isinstance(value, (str, int, float, bool)) or value is None else None


def json_text(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True)


def render_transcript(path: Path, document: dict[str, Any], digest: str) -> str:
    lines = [
        f"# Transcript `{digest}`",
        "",
        f"- Problem: `{document.get('problem_id', '')}`",
        f"- Recorded cost: `{document.get('actual_cost_usd', '')}`",
        f"- Calls: `{len(document.get('calls', []))}`",
        "",
    ]
    for index, call in enumerate(document.get("calls", []), 1):
        request = call.get("request") or {}
        model = request.get("model") or (call.get("response") or {}).get("model") or "unknown"
        lines.extend([
            f"## Call {index}: `{model}`",
            "",
            f"Status: `{call.get('status')}` · latency: `{call.get('latency_ms')}` ms · "
            f"cost: `{call.get('actual_cost_usd')}`",
            "",
        ])
        for position, message in enumerate(request.get("messages") or []):
            role = message.get("role", "unknown") if isinstance(message, dict) else "unknown"
            content = message.get("content", "") if isinstance(message, dict) else message
            lines.extend([
                f"<details><summary>Request message {position}: {html.escape(str(role))}</summary>",
                "",
                "````text",
                str(content),
                "````",
                "</details>",
                "",
            ])
        response = call.get("response") or {}
        choices = response.get("choices") or []
        message = choices[0].get("message", {}) if choices and isinstance(choices[0], dict) else {}
        lines.extend([
            "<details open><summary>Response</summary>",
            "",
            "````text",
            str(message.get("content") or ""),
            "````",
            "</details>",
            "",
        ])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", action="append", required=True, metavar="ID=PATH")
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--public-base-url", required=True)
    args = parser.parse_args()

    archives: list[tuple[str, Path]] = []
    for item in args.archive:
        archive_id, separator, raw_path = item.partition("=")
        if not separator or not archive_id or not raw_path:
            parser.error(f"invalid --archive value: {item!r}")
        root = Path(raw_path).resolve()
        if not root.is_dir():
            parser.error(f"archive does not exist: {root}")
        archives.append((archive_id, root))

    out = args.out.resolve()
    tables = out / "tables-jsonl"
    transcripts_out = out / "views" / "transcripts"
    tables.mkdir(parents=True, exist_ok=False)
    transcripts_out.mkdir(parents=True)

    file_rows: list[dict[str, Any]] = []
    run_rows: list[dict[str, Any]] = []
    recheck_rows: list[dict[str, Any]] = []
    transcript_rows: list[dict[str, Any]] = []
    call_rows: list[dict[str, Any]] = []
    message_rows: list[dict[str, Any]] = []
    attempt_rows: list[dict[str, Any]] = []
    packet_rows: list[dict[str, Any]] = []
    errors: list[dict[str, str]] = []
    rendered: set[str] = set()

    for archive_id, root in archives:
        for path in sorted(candidate for candidate in root.rglob("*") if candidate.is_file()):
            relative = path.relative_to(root)
            digest = sha256_file(path)
            stat = path.stat()
            host = source_host(relative)
            url = raw_url(args.public_base_url.rstrip("/"), archive_id, relative)
            file_rows.append({
                "archive_id": archive_id,
                "source_host": host,
                "source_relative_path": relative.as_posix(),
                "filename": path.name,
                "suffix": path.suffix.lower(),
                "size_bytes": stat.st_size,
                "source_mtime_ns": stat.st_mtime_ns,
                "source_mode": oct(stat.st_mode & 0o777),
                "sha256": digest,
                "media_type": mimetypes.guess_type(path.name)[0] or "application/octet-stream",
                "raw_url": url,
            })

            if path.name not in {"result.json", "transcript.json"}:
                continue
            try:
                document = load_json(path)
            except Exception as exc:
                errors.append({
                    "archive_id": archive_id,
                    "source_relative_path": relative.as_posix(),
                    "error": f"{type(exc).__name__}: {exc}",
                })
                continue

            record_id = hashlib.sha256(
                f"{archive_id}\0{relative.as_posix()}".encode()
            ).hexdigest()[:24]
            task = task_name(relative)

            if path.name == "result.json" and "status" in document:
                metadata = document.get("agent_metadata") or {}
                comparator = document.get("comparator") or {}
                budget = document.get("budget") or {}
                answer_shape = document.get("answer_shape") or {}
                run_rows.append({
                    "run_id": record_id,
                    "archive_id": archive_id,
                    "source_host": host,
                    "source_relative_path": relative.as_posix(),
                    "task": task,
                    "content_sha256": digest,
                    "raw_url": url,
                    "problem_id": document.get("problem_id"),
                    "status": document.get("status"),
                    "passed": document.get("passed"),
                    "points": document.get("points"),
                    "wall_s": document.get("wall_s"),
                    "within_time": document.get("within_time"),
                    "tier": document.get("tier"),
                    "cost_limit_usd": budget.get("limit_usd"),
                    "cost_spent_usd": budget.get("spent_usd"),
                    "cost_reserved_usd": budget.get("reserved_usd"),
                    "accounting_complete": budget.get("accounting_complete"),
                    "comparator_passed": comparator.get("passed"),
                    "comparator_timed_out": comparator.get("timed_out"),
                    "comparator_duration_ms": comparator.get("duration_ms"),
                    "comparator_exit_code": comparator.get("exit_code"),
                    "answer_shape_passed": answer_shape.get("passed"),
                    "agent_error": scalar(document.get("agent_error")),
                    "design_id": metadata.get("design_id"),
                    "condition": metadata.get("condition"),
                    "collaboration_strategy": metadata.get("collaboration_strategy"),
                    "scheduler": metadata.get("scheduler"),
                    "seed": metadata.get("seed"),
                    "selected_model": metadata.get("selected_model"),
                    "selection_reason": metadata.get("selection_reason"),
                    "calls_attempted": metadata.get("calls_attempted"),
                    "calls_dispatched": metadata.get("calls_dispatched"),
                    "physical_requests": metadata.get("physical_requests"),
                    "max_calls_per_model": metadata.get("max_calls_per_model"),
                    "dispatch_cutoff_s": metadata.get("dispatch_cutoff_s"),
                    "model_call_wall_timeout_s": metadata.get("model_call_wall_timeout_s"),
                    "models_used_json": json_text(document.get("models_used")),
                    "reasoning_effort_json": json_text(metadata.get("reasoning_effort_by_model")),
                })
                for model, track in (metadata.get("tracks") or {}).items():
                    for attempt in track.get("attempts") or []:
                        attempt_rows.append({
                            "run_id": record_id,
                            "archive_id": archive_id,
                            "source_host": host,
                            "problem_id": document.get("problem_id"),
                            "condition": metadata.get("condition"),
                            "model": model,
                            **{key: scalar(value) for key, value in attempt.items()},
                        })
                for index, packet in enumerate(metadata.get("packet_events") or []):
                    packet_rows.append({
                        "run_id": record_id,
                        "packet_index": index,
                        "archive_id": archive_id,
                        "source_host": host,
                        "problem_id": document.get("problem_id"),
                        "condition": metadata.get("condition"),
                        **{key: scalar(value) for key, value in packet.items()},
                        "packet_json": json_text(packet),
                    })
            elif path.name == "result.json" and "recovered" in document:
                verdict = document.get("comparator") or {}
                recheck_rows.append({
                    "recheck_id": record_id,
                    "archive_id": archive_id,
                    "source_host": host,
                    "source_relative_path": relative.as_posix(),
                    "task": document.get("task") or task,
                    "problem_id": document.get("problem_id"),
                    "candidate_sha256": document.get("candidate_sha256"),
                    "recovered": document.get("recovered"),
                    "passed": verdict.get("passed"),
                    "timed_out": verdict.get("timed_out"),
                    "duration_ms": verdict.get("duration_ms"),
                    "exit_code": verdict.get("exit_code"),
                    "attempts_json": json_text(document.get("attempts")),
                    "content_sha256": digest,
                    "raw_url": url,
                })
            elif path.name == "transcript.json" and "calls" in document:
                view_url = f"{args.public_base_url.rstrip('/')}/views/transcripts/{digest}.md"
                transcript_rows.append({
                    "transcript_id": record_id,
                    "archive_id": archive_id,
                    "source_host": host,
                    "source_relative_path": relative.as_posix(),
                    "task": task,
                    "problem_id": document.get("problem_id"),
                    "actual_cost_usd": document.get("actual_cost_usd"),
                    "call_count": len(document.get("calls") or []),
                    "content_sha256": digest,
                    "raw_url": url,
                    "rendered_url": view_url,
                })
                if digest not in rendered:
                    (transcripts_out / f"{digest}.md").write_text(
                        render_transcript(path, document, digest), encoding="utf-8"
                    )
                    rendered.add(digest)
                for call_index, call in enumerate(document.get("calls") or []):
                    request = call.get("request") or {}
                    response = call.get("response") or {}
                    choices = response.get("choices") or []
                    response_message = (
                        choices[0].get("message", {})
                        if choices and isinstance(choices[0], dict) else {}
                    )
                    call_rows.append({
                        "transcript_id": record_id,
                        "archive_id": archive_id,
                        "source_host": host,
                        "problem_id": document.get("problem_id"),
                        "call_index": call_index,
                        "call_id": call.get("call_id"),
                        "status": call.get("status"),
                        "started_at": call.get("started_at"),
                        "latency_ms": call.get("latency_ms"),
                        "actual_cost_usd": call.get("actual_cost_usd"),
                        "reserved_cost_usd": call.get("reserved_cost_usd"),
                        "model": request.get("model") or response.get("model"),
                        "provider": request.get("provider") or response.get("provider"),
                        "max_tokens": request.get("max_tokens"),
                        "temperature": request.get("temperature"),
                        "response_content": response_message.get("content"),
                        "response_reasoning": response_message.get("reasoning"),
                        "usage_json": json_text(response.get("usage")),
                        "request_json": json_text(request),
                        "response_json": json_text(response),
                    })
                    for message_index, message in enumerate(request.get("messages") or []):
                        if not isinstance(message, dict):
                            message = {"role": "unknown", "content": message}
                        message_rows.append({
                            "transcript_id": record_id,
                            "archive_id": archive_id,
                            "source_host": host,
                            "problem_id": document.get("problem_id"),
                            "call_index": call_index,
                            "message_index": message_index,
                            "direction": "request",
                            "role": message.get("role"),
                            "model": request.get("model"),
                            "content": str(message.get("content") or ""),
                        })
                    message_rows.append({
                        "transcript_id": record_id,
                        "archive_id": archive_id,
                        "source_host": host,
                        "problem_id": document.get("problem_id"),
                        "call_index": call_index,
                        "message_index": len(request.get("messages") or []),
                        "direction": "response",
                        "role": "assistant",
                        "model": request.get("model") or response.get("model"),
                        "content": str(response_message.get("content") or ""),
                    })

    datasets = {
        "files": file_rows,
        "runs": run_rows,
        "candidate_rechecks": recheck_rows,
        "transcripts": transcript_rows,
        "calls": call_rows,
        "messages": message_rows,
        "attempts": attempt_rows,
        "packet_events": packet_rows,
        "conversion_errors": errors,
    }
    counts = {name: dump_jsonl(tables / f"{name}.jsonl", rows) for name, rows in datasets.items()}
    catalog = {
        "schema_version": 1,
        "title": "RE Take-Home Agent Trajectories and Evaluation Evidence",
        "description": "Public, non-destructive derivatives and immutable raw archives from Lean proving-agent experiments.",
        "public_base_url": args.public_base_url.rstrip("/"),
        "archives": [{"archive_id": name, "source_path": str(path)} for name, path in archives],
        "counts": counts,
        "tables": {
            name: f"{args.public_base_url.rstrip('/')}/derived/v1/{name}.parquet"
            for name in datasets
        },
        "raw_policy": "Derived tables never replace raw files. Raw paths and SHA-256 values are recorded in files.parquet.",
    }
    (out / "catalog.json").write_text(
        json.dumps(catalog, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    links = "\n".join(
        f'<li><a href="derived/v1/{html.escape(name)}.parquet">{html.escape(name)}.parquet</a> — {count:,} rows</li>'
        for name, count in counts.items()
    )
    (out / "index.html").write_text(f"""<!doctype html>
<meta charset="utf-8">
<title>RE Take-Home Evidence</title>
<style>body{{font:16px system-ui;max-width:900px;margin:3rem auto;padding:0 1rem;line-height:1.5}}code{{background:#eee;padding:.15rem .3rem}}li{{margin:.35rem 0}}</style>
<h1>RE Take-Home Agent Trajectories and Evaluation Evidence</h1>
<p>This site exposes immutable raw experiment artifacts together with non-destructive Parquet indexes and readable transcript views.</p>
<p><a href="catalog.json">Machine-readable catalog</a></p>
<h2>Derived tables</h2><ul>{links}</ul>
<h2>Integrity</h2>
<p>Every derived record links to its raw source path and SHA-256. Parquet and Markdown files are conveniences; they do not replace the original JSON, Lean, log, or configuration files.</p>
""", encoding="utf-8")
    print(json.dumps({"counts": counts, "rendered_unique_transcripts": len(rendered)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
