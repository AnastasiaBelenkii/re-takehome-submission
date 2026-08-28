# Baseline controls, two-replicate wave

## Purpose

Complete a compact, reusable baseline suite before the collaboration study.
This is a descriptive control wave, not a confirmatory hypothesis test.  It
measures stock single-model repair, a no-communication two-model portfolio,
and single-model depth controls under a common full-sample regime.

This memo was committed before any new wave run was launched.  Historical
outcomes were already visible, so no claim of blinded preregistration is made.

## Conditions

| Condition | Agent behavior | Per-model call ceiling |
|---|---|---:|
| `qwen-stock-25` | Supplied `SimpleBaselineAgent`, Qwen | 25 |
| `gpt-stock-25` | Supplied `SimpleBaselineAgent`, GPT-OSS | 25 |
| `independent-portfolio-25x2` | Existing synchronized independent-repair portfolio; stock policy on both tracks; no information crosses tracks | 25 each |
| `qwen-stock-50` | Supplied `SimpleBaselineAgent`, Qwen; horizon only changed | 50 |
| `gpt-stock-50` | Supplied `SimpleBaselineAgent`, GPT-OSS; horizon only changed | 50 |

The 50-call solos are call-ceiling controls for the portfolio's maximum 50
calls.  They are not matched on model mixture, realized calls, tokens, cost,
latency, or parallelism.  Their prompt truthfully reports a 50-turn horizon,
so turn 25 is no longer described as the final attempt.

The portfolio instantiates the supplied baseline configuration twice and
reuses its prompt, extraction, and feedback functions.  Model calls in a round
are concurrent, Lean checks are serialized in fixed model order, failures are
isolated by track, and selection is deterministic.  It does not literally run
two asynchronous calls to `SimpleBaselineAgent.solve` and must be described as
a synchronized baseline-equivalent portfolio.

## Replication target and existing evidence

Target: exactly two primary replicates per condition.

- `qwen-stock-25` replicate 1 is the post-fix refresh launched at
  `20260827T220951.071990Z`, run timestamp `20260827T221008Z`.
- `gpt-stock-25` replicate 1 is the same refresh, run timestamp
  `20260827T233401Z`.
- `independent-portfolio-25x2` replicate 1 is the completed evidence run
  launched at `20260826T204631Z`, run timestamp `20260826T204645Z`.  It used one
  outer worker and a legacy launcher without manifest/problem hashes; those
  infrastructure differences must be disclosed, but its pinned commit,
  effective environment, complete 16-problem artifacts, and exact agent code
  are recorded.
- All other primary replicates are new, requiring seven new full runs total:
  one stock-25 run per model, one portfolio run, and two stock-50 runs per model.

Repetitions are independent stochastic replicates, not explicit provider
seeds.  The stock agent does not pass `seed`; changing that would make the new
requests differ from the existing stock replicate, while provider routing also
precludes a claim of bitwise reproducibility.

## Frozen common regime

- All 16 checked-in sample problems.
- 1 point per Comparator-passing problem.
- 20-minute outer limit per problem.
- 2-minute final-verification reserve.
- $1.00 shared problem budget.
- 12,000 maximum output tokens per call.
- Temperature 0.2.
- Two independent outer problem workers per machine.
- Lean checks: 120 seconds; Comparator: 180 seconds.
- Pinned supplied Lean image digest.
- Exactly one condition-run per droplet at a time.
- New runs launched together from detached worktrees at one frozen commit.

Maximum calls are matched where declared.  Realized calls, cost, tokens, and
wall time may differ because of early success, latency, errors, and external
caps.  `cost_unknown`, timeouts, failures, and zero scores remain valid outcomes
when artifact integrity succeeds.

## Artifact and revision rules

- Checked-in manifests are authoritative inputs.
- Every run records commit, agent hash, manifest hash, sample-manifest hash,
  launcher hash, host, exact command, and effective environment before launch.
- Existing and new raw bundles are immutable and retained outside Git.
- Git stores manifests, an append-only run index, validation reports, checksums,
  and derived paper tables; it does not store bulky transcripts.
- A run counts only after validation finds 16 non-missing problem results and
  the declared model/call contract.
- Interrupted runs are resumed when safe; observed scores never justify a
  configuration change or selective rerun.
- Code exercised by a launched run is never mutated for that wave.  Corrections
  to derived analysis preserve the original output and record input hashes.
