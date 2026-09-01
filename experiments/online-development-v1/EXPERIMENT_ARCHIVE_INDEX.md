# Consolidated experiment archive index

## Canonical location

As of 2026-09-01, the canonical human-controlled snapshot of experimental
artifacts from all ten droplets is:

```text
takehome-worker-9:/opt/human-loop-archive/experimental-results-20260901T022218Z
```

Worker 9 is reserved for human-directed canaries, debugging, judge checks, and
archive access. Worker 10 is the machine-controlled Humanize coordinator and is
not the canonical archive host.

The snapshot is additive and non-mutating: source results remain on their
original workers. A partial, non-canonical copy created before the allocation
was clarified remains on worker 1 at the same absolute archive path. Do not use
that partial copy as the evidence source.

## Layout

Each source host has an independent namespace so equal run names cannot
overwrite one another:

```text
experimental-results-20260901T022218Z/
└── hosts/
    ├── takehome-worker-1/
    │   ├── opt/
    │   └── root/re-takehome/
    ├── ...
    └── takehome-worker-10/
```

Within each host namespace, the archive retains these result-bearing roots
when present:

- `/opt/takehome-results`
- `/opt/experiments`
- `/opt/online-development-v1-stage*`
- `/opt/takehome-concurrency-canary/results`
- `/root/re-takehome/outputs`
- `/root/re-takehome/experiments`

The `/opt/experiments` snapshots include run-local code and provenance needed
to interpret their outputs. The host namespace is therefore part of every
artifact reference and must not be discarded during later deduplication.

## Transfer inventory

The following counts use `transcript.json`, `events.jsonl`, `result.json`, and
`summary.json` as artifact markers. They are file counts, not unique-run counts;
some historical launchers deliberately copied the same run into both a run
directory and `/opt/takehome-results`.

| Source | Snapshot bytes | Artifact markers |
|---|---:|---:|
| takehome-worker-1 | 428,003,513 | 1,786 |
| takehome-worker-2 | 203,763,439 | 973 |
| takehome-worker-3 | 169,084,303 | 983 |
| takehome-worker-4 | 167,282,292 | 928 |
| takehome-worker-5 | 160,006,287 | 928 |
| takehome-worker-6 | 58,376,394 | 461 |
| takehome-worker-7 | 57,668,050 | 473 |
| takehome-worker-8 | 57,727,475 | 469 |
| takehome-worker-9 | 59,239,292 | 469 |
| takehome-worker-10 | 57,072,768 | 449 |
| **Total** | **1,418,223,813** | **7,919** |

After transfer, each host namespace passed an rsync checksum-mode dry
comparison against its relay snapshot with no reported difference.
The destination contained ten host directories, zero `.env` files, and zero
rsync partial files. The source trees were not deleted or mutated.

## Credential and scope boundary

The transfer deliberately excludes `.env`, `.git`, virtual environments,
Python caches, and directories named `secrets`. It also excludes worker 10's
`/opt/humanize-pilot` installation. That installation contains controller
credentials and is operational state, not an experiment-results root.

The exclusions protect credentials without stripping transcript, event,
result, summary, log, provenance, condition, or run metadata files from the
selected roots. No source artifact was deleted after copying.

## Retrieval examples

List every transcript associated with worker 7:

```bash
ssh takehome-worker-9 \
  "find /opt/human-loop-archive/experimental-results-20260901T022218Z/hosts/takehome-worker-7 -name transcript.json -print"
```

Search all archived event streams for a call identifier or failure string:

```bash
ssh takehome-worker-9 \
  "rg -n 'SEARCH_TERM' /opt/human-loop-archive/experimental-results-20260901T022218Z/hosts"
```

Copy one immutable host snapshot locally without changing the archive:

```bash
rsync -a --partial \
  takehome-worker-9:/opt/human-loop-archive/experimental-results-20260901T022218Z/hosts/takehome-worker-7/ \
  ./takehome-worker-7-artifacts/
```

## Interpretation rules

- Reference artifacts by canonical archive path, source host, and original run
  path.
- Treat duplicate copies as provenance-preserving mirrors, not independent
  observations.
- Do not collapse results across conditions or commits until their provenance,
  manifests, problem hashes, model settings, and evaluator paths agree.
- Preserve incomplete, failed, timed-out, and gate-rejected runs: their
  transcripts are part of the substrate audit evidence.
- The archive is a snapshot, not a live results database. Later runs require a
  new timestamped snapshot or an explicitly documented append-only update.
