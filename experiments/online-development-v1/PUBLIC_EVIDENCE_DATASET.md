# Public experiment evidence

The September 1 consolidated archive and September 2 matched Stage 3 supplement
are published as public-read objects at:

<https://vm-re-takehome-data.sfo3.digitaloceanspaces.com/index.html>

The publication is additive. Source archives remain byte-for-byte intact on the
archive host. Queryable Parquet tables and Markdown transcript views are derived
copies; they do not replace the original JSON, JSONL, Lean, log, or provenance
files. Compressed preservation bundles contain copies of the original archive
trees and their checksum manifests.

## Fast remote access

The machine-readable catalog is:

<https://vm-re-takehome-data.sfo3.digitaloceanspaces.com/catalog.json>

DuckDB can query the tables without downloading the full archive:

```sql
SELECT condition, count(*) AS runs, sum(points) AS points
FROM read_parquet(
  'https://vm-re-takehome-data.sfo3.digitaloceanspaces.com/derived/v1/runs.parquet'
)
GROUP BY condition
ORDER BY condition;
```

Important object prefixes are:

- `derived/v1/` — normalized Parquet tables;
- `views/transcripts/` — content-deduplicated, readable Markdown transcripts;
- `raw/extracted/legacy-20260901/` — original September 1 archive files;
- `raw/extracted/matched-stage3-20260902/` — original September 2 supplement;
- `raw/snapshots/` — compressed byte-preservation copies and SHA-256 manifest.

Every published object is uploaded with a `public-read` ACL. The bucket itself
does not expose anonymous directory listing, so use the catalog, this index, a
known object URL, or the Git evidence manifests as the entry point.

## Git ancestry links

For every archived run with an explicit `git_commit` in `provenance.json`, the
repository publishes an `evidence/run-data-<12-character-sha>` branch. Its tip
is a one-commit direct child of that exact generating commit. The evidence
commit adds:

- `evidence/ARCHIVE_POINTER.json`, with per-run public URLs and provenance
  SHA-256 values; and
- `evidence/transcripts/<sha256>.json`, containing the associated raw transcript
  payloads as ordinary Git blobs;
- `evidence/TRANSCRIPT_INDEX.json`, mapping original archive paths to those
  content-addressed Git files; and
- `evidence/README.md`, explaining the relationship.

The associated transcripts are therefore accessible in environments that can
fetch GitHub but cannot reach DigitalOcean Spaces. The rest of the large raw
archive is intentionally not stored as Git blobs. This keeps ordinary branch
checkouts focused while making the code-to-data relationship verifiable with
`git rev-parse evidence/run-data-<sha>^`.

Historical artifacts that do not contain an explicit full commit SHA remain in
the public catalog and raw archive but are not assigned to a Git ancestry branch
by inference.

The complete branch-to-parent mapping is recorded in
[GIT_EVIDENCE_REFS.md](GIT_EVIDENCE_REFS.md).

For agents that need one Git-only entry point, the
`evidence/all-transcripts-20260902` branch contains all 485 unique raw
transcripts covering all 2,564 archived transcript paths, including historical
files without exact commit provenance. Its content-addressed files and
`evidence/TRANSCRIPT_INDEX.json` can be used without DigitalOcean access. This
convenience branch must not be used to infer generating commits; use the 13
per-commit branches for that relationship.

## Interpretation

Multiple archive paths can be mirrors of the same result. Use `content_sha256`
and provenance before treating rows as independent trials. Failed, incomplete,
timed-out, and locally gate-rejected results are retained because they are part
of the audit evidence.
