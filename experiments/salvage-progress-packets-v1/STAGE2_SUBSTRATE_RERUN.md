# Stage 2 substrate repair and corrected rerun

## Scope

This addendum closes the treatment-neutral defects exposed by the first
`p06_pow_mod`, seed 1729, four-calls-per-model C0+/C1+ microcell. The
collaboration conditions were not changed.

The common repair at `973ce4447aa07e985f346226d01cb75c1fb77634`:

- runs at most one intermediate fresh Comparator at a time;
- keeps only the latest not-yet-started warm-valid candidate;
- deduplicates candidates by normalized-source hash;
- lets independent model calls proceed while Comparator runs;
- preserves the final clean Comparator as authoritative;
- imposes a 420-second whole-semantic-call deadline in addition to httpx's
  per-operation timeouts, with uncertain spend recorded on cancellation; and
- force-cleans an exact verifier session if its coroutine is cancelled.

Offline validation passed 113 tests plus all nine opt-in pinned-image Docker
tests. The sole full-suite failure remains the pre-existing frozen historical
baseline-manifest hash check.

## First repair rerun and newly exposed fallback bug

The first repaired pair used `973ce44`. C1+ passed in 359.982 seconds. It
dispatched a further model call 13 ms after a candidate passed warm Lean while
the 165.463-second intermediate Comparator was active. A byte-identical later
candidate was deduplicated rather than checked again.

C0+ appeared to fail in 623.042 seconds, but that outcome is invalid as a
solver result. GPT call 4 passed warm Lean and its intermediate Comparator
timed out. A ranking error then returned the rejected deterministic call-zero
candidate instead of the warm-valid model proof. Final Comparator therefore
judged malformed source containing `p06_answer := first | ...`, not GPT's
candidate.

This revealed two universal defects, fixed at
`b33d11df6dd46aa8270b2be19a903b8a7b9ea03a`:

1. a provisional warm-valid candidate now strictly outranks every Lean-failed
   candidate, irrespective of warning/diagnostic counts; and
2. deterministic tactic substitution is skipped for files containing term
   holes such as `abbrev p06_answer : Nat := sorry`. The tactic cascade remains
   unchanged for ordinary proof holes such as `:= by sorry`.

A regression test confirms that a warm-valid candidate remains the final
fallback even if intermediate fresh verification fails or times out.

## Final corrected matched pair

Frozen settings were identical across arms: `p06_pow_mod`, seed 1729, four
calls/model, $0.25 cap, 1,200-second outer limit, 720-second dispatch cutoff,
180-second Comparator timeout, two-second salvage checks, and 420-second model
call wall deadline.

| Arm | Passed | Calls | Wall seconds | Spend | Useful salvage skeletons |
| --- | ---: | ---: | ---: | ---: | ---: |
| C0+ | no | 8 | 297.299 | $0.005853585 | 3 |
| C1+ | yes | 8 | 326.526 | $0.003848350 | 1 |

C0+ returned a genuine GPT model checkpoint with a valid literal answer
shape. Final Comparator completed in 111.141 seconds and rejected the
incomplete proof. No deterministic call-zero candidate was created.

C1+ produced three warm-valid candidates. The single active verifier checked
Qwen call 2 and passed in 179.198 seconds; a queued GPT candidate was replaced
by a newer Qwen candidate, which was then dropped when the active candidate
passed. Final independent Comparator passed in 113.358 seconds.

The C1+ score is **not collaboration-uplift evidence**. Its winning Qwen call 2
used no peer packet. One progress packet was generated only after round 3 and
was never consumed. Qwen call 1 was byte-identical across C0+ and C1+, but its
second response diverged despite identical no-packet inputs, so ordinary
provider nondeterminism can explain the 0-1 split.

## Decision

The asynchronous verifier, latest-wins bound, hash deduplication, final-judge
authority, and model-call deadline passed their online canary. The corrected
fallback also behaved as intended. This closes the known treatment-neutral
substrate blockers found in this wave.

Do not cite this pair as a treatment comparison. The next paid stage should
move to harder, less saturated problems and include enough matched restarts to
observe packet consumption and distinguish collaboration effects from
provider variance. `putnam_2020_a2` remains the first recommended hard cell
because offline salvage yield was high there.

## Artifacts

- `stage2-rerun/artifacts/`: first asynchronous-verifier rerun at `973ce44`,
  retained because it exposed the fallback bug.
- `stage2-final/artifacts/`: final corrected matched pair at `b33d11d`.
- `stage2-rerun/dispatch/` and `stage2-final/dispatch/`: exact frozen cell
  descriptors.
- Remote final root:
  `/opt/salvage-progress-packets-v1-stage2-final-20260902T053000Z` on workers 8
  and 9. Both cells are terminal; no experiment process or container remains.
