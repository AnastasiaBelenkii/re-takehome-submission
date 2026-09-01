# Online development v1

This prospective development line starts from corrected-challenge commit
`e1c8fee`. It does not modify C0/C1/C2 strategy definitions. Its first revision
changes only shared candidate-safety, verification, state, and deadline
infrastructure.

## Common-substrate revision

- Required challenge declarations must appear exactly once with unchanged
  normalized headers; additional fresh helper declarations are allowed.
- Candidate imports are deterministically canonicalized to `import Mathlib`
  before Lean checking, state commit, checkpointing, packet observation, and
  return.
- Gate-rejected proposals remain records only. They cannot replace current
  repair state, checkpoints, or peer packet source code.
- Inadmissible proposals rank below every admissible Lean-checked candidate.
- The final verification reserve covers the configured Comparator timeout plus
  a 30-second shutdown/serialization margin, subject to a 25% cap for short
  development runs.
- Warm Lean and submitted candidates use the same canonical `Mathlib` import
  context for this controller.

## Stage 0

`stage0-p09-contract-replay.json` reclassifies the three archived deep
`p09_imo1964` trajectories. Among 1,281 recoverable textual outputs:

- old whole-declaration-list gate rejections: 1,118;
- current required-declaration rejections: 539;
- newly admitted helper-bearing proposals: 579;
- responses whose imports require deterministic canonicalization: 955.

This replay classifies recorded responses; it is not a counterfactual model
trajectory after transactional state changes.

## Stage 1

- 21 focused controller, runner, configuration, and REPL-protocol tests passed.
- Seven real pinned-image Docker integration tests passed in 231.50 seconds.
- The corrected challenge branch intentionally fails the historical
  solo-baseline-refresh byte-hash test because that frozen experiment pins the
  original defective problem manifest. The guard is retained rather than
  weakened.

## Stage 2 plan

Use corrected `p09_imo1964`, `p10_factorial_pow`, and `putnam_2020_a2` under
unchanged C0/C1/C2 strategies, with six calls per model and a short declared
development envelope. These nine cells are integration microcells, not an
evaluation score estimate. Rolling analysis will report calls, gate outcomes,
exact final verdict, checkpoint changes, packet exposure, cost, and latency.

### Initial deployment canary

The first nine-host launch at commit `16f65f6` made no model calls. Shared
remote virtual environments contained editable-install pointers to older host
checkouts, so `run.py` resolved stale `re_harness` modules and the v2 agent
failed to import. Those cells are infrastructure canary failures, not stage-2
outcomes. The launcher now sets `PYTHONPATH` explicitly to the frozen task
checkout. Relaunch requires a remote import-origin preflight and distinct task
IDs; failed artifacts remain immutable.

The stale import failed before any provider request, so all nine canaries have
zero calls and zero spend. The worker nevertheless ran Comparator against the
pristine fallback challenge, adding 115--181 seconds to every failed cell.
`run.py` also exited zero after emitting a `harness_error` result. Future
orchestration must therefore classify the result artifact rather than treating
a zero launcher exit code as scientific success.

## Stage 2 relaunch findings

All nine matched microcells ran from commit `2eca929` after import-origin
preflight on each host. None solved its problem. Eight ended as ordinary failed
proofs; `p09_imo1964` C2 ended `cost_unknown` when the agent deadline cancelled
an in-flight GPT request after 315.9 seconds. That cell is not a valid
condition comparison.

There was no observed endpoint rate-limit failure: 49 Qwen and 48 GPT calls
completed with zero 429 retries. Qwen latency had a 39.0-second median and
69.5-second maximum; GPT latency had a 67.5-second median and 257.3-second
maximum. Per-round lockstep made each track wait for the slower peer. This
caused matched cells to obtain different call counts: C0/C1/C2 received
12/10/8 calls on `p09_imo1964`, while the latter two hit the dispatch cutoff or
agent deadline. The observed time bottleneck is therefore the GPT long tail
combined with lockstep scheduling, not evidence of a Qwen concurrency ceiling.

The revised source-text declaration gate rejected eight proposals. Four were
genuinely incomplete (no complete required file); four were false positives:

- two `putnam_2020_a2` GPT proposals used `Icc` after `open Finset` instead of
  spelling `Finset.Icc` in the required theorem;
- one `p09_imo1964` Qwen proposal changed an unused hypothesis binder from
  `hn` to `_`;
- one `p09_imo1964` GPT proposal inserted whitespace between `¬` and `7`.

Those spellings elaborate to the same required types. The proposals happened
not to solve their problems, but rejecting them before Lean is still the wrong
contract decision. Exact normalized source headers remain too strict and are a
stage-2 stop condition. Do not scale this revision until the gate validates
required declaration types semantically (or safely reconstructs pristine
headers) and regression tests cover qualification, binder, and whitespace
equivalence.

## Provisional-success revision

The next common-substrate revision removes source-text header equality from the
live decision path. A cheap transactional guard now requires each manifest
declaration name exactly once with a compatible declaration kind. It does not
decide whether theorem types are semantically equal. The legacy textual
classifier remains available only for audit replay.

Warm-REPL success is provisional. The worker exposes an event-logged verifier
that runs numeric-answer-shape checks and the real Comparator in a fresh,
separately identified container. Only a candidate passing both may stop the
agent or receive a `fresh_comparator_passed` checkpoint. Warm failures can be
saved for crash recovery only as `provisional_lean_failure`; a warm success
rejected by fresh verification remains local repair state and cannot displace
the global best checkpoint. Final judging remains a second fresh Comparator
run after the agent returns.

`stage0-p09-structural-gate-replay.json` applies the new completeness guard to
the same three archived deep p09 transcripts. Of 1,281 textual outputs, the
exact-header gate rejected 539 while the structural guard rejects 67. The 472
released proposals go to Lean; only a warm success among them incurs fresh
Comparator verification. This replay is classification, not a counterfactual
trajectory.

Focused tests pass, and the initial pinned-image stage accepted a valid proof,
rejected a changed statement and forbidden axiom, rejected both corrected
Putnam circular solutions, and demonstrated that in-agent fresh verification
and final judging agree. The strengthened worker regression also checks that
the warm REPL remains usable after the separately scoped Comparator run.
