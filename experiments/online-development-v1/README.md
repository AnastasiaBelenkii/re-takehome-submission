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
