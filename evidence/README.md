# Evaluator endpoint evidence

This branch preserves every archived `result.json`, `events.jsonl`, `provenance.json`, and `preliminary-status.json` at its original path beneath an archive namespace. These files supply Lean and Comparator outcomes that are not present in call transcripts.

- `archives/legacy-20260901/` is the September 1 consolidated snapshot.
- `archives/matched-stage3-20260902/` is the September 2 matched Stage 3 supplement.
- `ENDPOINT_INDEX.json` records every Git path, byte size, and SHA-256.

Duplicate archive mirrors retain distinct paths but share identical Git blob objects. No artifact has been transformed.
