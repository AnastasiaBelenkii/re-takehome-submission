# Overnight C0/C1/C2 Execution Plan

## Summary

Implement and freeze the shared base immediately, obtain the first usable C0/C1/C2 outcomes through a production sentinel within roughly one task duration, then continue autonomously through:

1. Three replicated shallow runs on a six-problem core
2. One shallow breadth run on the other nine valid problems
3. Judge-depth C0/C1/C2 runs on two predeclared hard problems

The controller never exceeds four active problems, preserving the empirically clean four-requests-per-model envelope.

Copy this complete plan into `experiments/collaboration-engine-v2/PLAN.md` before implementation and commit it with the experiment. Preserve the original plan text; record later operational deviations in an append-only section with timestamps and reasons.

## Frozen Base and Conditions

Shared base in every arm:

- Generic deterministic tactic cascade before model calls
- Bounded retries only for typed, explicitly cost-free 429s
- Inline 3–8-line proof sketch as Lean comments on direct/restart generations
- Existing D stagnation detection, failure memory, and two diversified restarts
- Immutable declarations/numeric answers and best-candidate checkpoints
- Paired logged seeds, temperature 0.2, 12k generation tokens

Conditions:

- **C0:** no peer packets
- **C1:** one reciprocal packet pair after the first eligible dual-failure round
- **C2:** one reciprocal packet pair after every eligible dual-failure round

Strategies cannot add calls, alter scheduling, access services, or mutate solver state.

## De-risking and First-Hour Signal

Create `collaboration-engine-v2` from the existing factorized collaboration commit; leave `main` and prior evidence untouched.

Before paid execution:

- Test tactic substitution against all pristine challenges and verify declarations remain unchanged.
- Simulate successful tactics, failed tactics, cost-free 429 retries, uncertain-spend failures, restarts, cutoff behavior, and checkpoints.
- Assert C0/C1/C2 first-round requests are byte-identical for the same problem and seed.
- Assert manifests differ only by condition and strategy.
- Test C1’s one-shot cadence and C2’s repeated cadence with partial rounds, model errors, timeouts, and accepted candidates.
- Run the full test suite and no-key smoke test.

The first paid production block is:

- Problem: `rmo_2000_2`
- Replication: 1
- Conditions: C0, C1, C2 concurrently
- Exact production commit, manifests, resources, and artifact schema

These are not throwaway canaries; they count in the matrix if validation passes. After completion, automatically verify:

- complete artifact/provenance contract
- no secrets or missing statuses
- semantic/physical call reconciliation
- C0 zero packets
- C1 at most one eligible reciprocal pair
- C2 one pair after every eligible round
- statement preservation
- independent 180-second Comparator recheck

If integrity fails, preserve the run, make only a generic integrity fix on a new commit, document it, and rerun the sentinel. Never rerun because of an undesirable score.

## Resource and Timeout Contract

### Shallow tasks

- Outer limit: 28 minutes
- New-round dispatch cutoff: 16 minutes
- Agent wrapper time: 25 minutes
- Comparator reserve: 3 minutes
- Maximum: 25 semantic calls/model and $1/problem

The nine-minute post-dispatch allowance covers bounded retry delay, a final three-minute model request, and two sequential Lean checks. Comparator always receives its full three minutes.

### Deep tasks

- Outer limit: 8 hours
- New-round dispatch cutoff: 7 hours 48 minutes
- No internal semantic-call ceiling; external time and $1 ledger bind
- Final 12 minutes reserved for in-flight work, Lean checks, and Comparator

No new requests start near the wall. This specifically prevents normal finalization from being mislabeled through cancellation-driven ledger closure.

## Autonomous Queue

Use four long-lived remote task slots with frozen worktrees and a resumable controller. State is persisted before each paid dispatch; mathematical failures are never automatically repeated.

### Stage 1: replicated core

Three replications per condition on:

- `p03_sq_ge_two_ab`
- `p06_pow_mod`
- `p07_least_divisible`
- `p10_factorial_pow`
- `putnam_2020_a2`
- `rmo_2000_2`

The sentinel supplies the first three cells. Remaining tasks are interleaved by a frozen deterministic schedule so condition is not aligned with provider weather.

### Stage 2: simultaneous deep tail and breadth

After the core validates:

- Allocate three slots to deep C0/C1/C2 tasks.
- Allocate one slot to the shallow breadth queue.
- Deep problems are predeclared as:

  - `p09_imo1964`
  - `rmo_2000_2`

- Each deep condition/problem pair runs once, giving six deep cells in two eight-hour waves.
- Breadth runs C0/C1/C2 once on the nine remaining valid problems.
- `rmo_2000_6` is never run and is reported as a dataset defect.

At worst, the replicated core takes about 6.3 hours after launch; the deep tail and breadth then complete together in approximately another 16 hours.

## Validation and Morning Outputs

Preserve raw outcomes without rewriting them. Produce separate fields for:

- mechanical pass
- full-180-second proof-validity recheck
- accounting completeness
- cost-free 429 retries
- uncertain-spend failure
- agent timeout
- outer timeout
- Comparator timeout
- late in-flight cancellation

A Comparator timeout never explains `cost_unknown`; both may co-occur and are reported independently. Primary intention-to-treat scores retain all failures. Sensitivity tables separately show proof-valid rechecks and accounting-complete tasks.

Automatically emit:

- sentinel status report as soon as available
- core per-problem scores out of three
- breadth scores out of one
- deep C0/C1/C2 table
- C1−C0, C2−C0, and C2−C1 paired contrasts
- calls, wall time, cost, tokens, retries, and latency
- deterministic call-zero solves
- pre/post-communication solve phase
- packet cadence, restarts, model contribution, diversity, and error-signature changes
- compact `MORNING.md`, CSV/JSON matrices, validation reports, commit hashes, manifests, and deviations log

Full artifacts remain in a checksummed external archive; only compact provenance and analysis outputs enter Git.

## Assumptions

- Shallow results characterize this bounded experimental regime and are not extrapolated numerically to hundreds of calls.
- Deep results are deployment-scale case studies on two predeclared problems, not a statistically powered score estimate.
- Existing pilot results are contextual and are not pooled with v2 because the shared base and timeout/retry substrate changed.
- `main` remains untouched overnight. The selected strategy is promoted into the externally limited judged agent only after reviewing the matrix.

## Operational deviations (append-only)

