# Uplift Pilot v1

## Predeclared purpose and hypothesis

This exploratory four-cell solo-agent tournament chooses one common
within-model uplift policy before collaboration is studied. It is not a
confirmatory causal study. The hypothesis is that either adaptive
planning/decomposition (P) or diversified restart (D), applied identically to
both allowed models over shared diagnostic substrate H, will improve the
six-problem solo score and/or problem coverage enough to justify freezing one
simple policy as `U*`.

The judged `submission` agent and the existing independent-portfolio control
are outside this experiment and are not modified or rerun by it.

## Conditions and policies

The four authoritative static manifests under `conditions/` define:

| Condition | Model | Policy |
|---|---|---|
| `qwen-p` | `qwen/qwen3.5-flash-02-23` | P |
| `gpt-p` | `openai/gpt-oss-120b` | P |
| `qwen-d` | `qwen/qwen3.5-flash-02-23` | D |
| `gpt-d` | `openai/gpt-oss-120b` | D |

H records bounded deduplicated diagnostics while the harness preserves raw
events, normalized candidate hashes and error signatures, best checkpoints, a
25-dispatched-call ceiling, and per-attempt metadata. H may record stagnation
but does not react to it.

P makes a direct complete-Lean attempt. Immediately after its first failed
Lean check it spends exactly one of its model calls on a structured strategy
memo (at most 2,500 requested output tokens), then generates and repairs
complete Lean files conditioned on that memo. The memo is never sent to Lean.
P has no diversified restart path.

D makes a direct attempt and ordinary feedback repair. An exactly repeated
normalized candidate triggers stagnation immediately; an unchanged normalized
error signature must persist across two transitions before triggering. D then
starts from the pristine theorem with bounded failed-approach memory and a
requirement for a materially different strategy. It permits at most two
restarts, preserves a better prior checkpoint, and makes no separate planning
call.

## Problem set and resource envelope

`problems.txt` contains exactly the six predeclared problems. Every condition
uses 20 minutes outer wall time per problem, including a two-minute verification
reserve (18 minutes available to the agent), $1.00 per problem, at most 25
dispatched model calls, 12,000 requested output tokens for proof generation or
repair, temperature 0.2, two independent outer problem workers, and the same
pinned Lean image and verification settings. Failed, cancelled, and uncertain-
cost calls count toward the call ceiling. `cost_unknown`, timeouts, proof
failures, model errors, and zero scores are valid outcomes when their artifacts
and provenance are complete.

The four conditions are intended to run concurrently on separate machines,
with no machine crossover. Real runs use pinned commits and launcher-created
detached worktrees. A runtime `.env` is copied into the worktree with mode 0600
and never into the result bundle.

## Collection and evidence rule

Each worker writes a self-contained immutable bundle locally. Collection uses
`scripts/collect_uplift_pilot.py`, which invokes `rsync --partial` into a hidden
resumable staging directory, atomically publishes a completed local copy, and
never mutates the remote bundle. `scripts/validate_uplift_pilot.py` checks provenance,
limits, models, all six problem artifacts, event/transcript/result/summary
agreement, call ceilings, secret patterns, and checksums. A bundle is evidence
only when validation succeeds. Invalid and interrupted bundles remain
preserved with their reasons.

`runs.jsonl` is an append-only compact index. Entries contain identifiers,
condition, commit, host, timestamps, status, validation outcome, score, cost,
and artifact path, never complete transcripts.

After all four bundles pass validation, `scripts/analyze_uplift_pilot.py`
calculates the predeclared model scores, policy score sums, virtual unions,
per-problem complementarity, calls, tokens, cost, wall time, timeout counts,
planning calls, and restart behavior. It refuses missing or invalid cells.

For an unattended concurrent wave, run `scripts/run_uplift_wave.py` inside
tmux with the exact commit, archive/state paths, four explicit
`CONDITION=SSH_HOST` mappings, and its literal paid-launch confirmation. It
writes state before dispatch, launches each cell at most once, monitors to a
terminal state, collects, validates, appends the ledger, and analyzes only four
valid bundles. Re-running the same command with an existing state file is
resume-only and can never automatically retry a paid launch.

Example (replace the commit and archive location deliberately):

```bash
python3 scripts/run_uplift_wave.py \
  --commit FULL_40_CHARACTER_COMMIT \
  --state /opt/takehome-archive/uplift-wave/state.json \
  --archive-root /opt/takehome-archive/uplift-wave \
  --cell qwen-p=takehome-worker-2 \
  --cell gpt-p=takehome-worker-3 \
  --cell qwen-d=takehome-worker-4 \
  --cell gpt-d=takehome-worker-5b \
  --confirm-paid-launch I_UNDERSTAND_THIS_LAUNCHES_PAID_RUNS
```

## Predeclared selection and revision rule

For each policy, calculate each model's solo score, the sum of solo scores, the
virtual Qwen-or-GPT problem union, per-problem complementarity, calls, tokens,
cost, wall time, timeouts, and stagnation behavior. Promote a clear standalone
winner shared by both models. Prefer the simpler policy when effectively tied.

Test P+D only when P and D have credible unique successes aligned with their
intended mechanisms. P+D receives the same 25-call ceiling and must beat, not
tie, the standalone leader. Permit at most one generic revision, only when the
same failure occurs on at least two problems and the change contains no
problem-specific information. After selection, freeze `U*`; later confirmation
uses the actual independent two-model portfolio on all 16 problems at the full
20-minute regime. Collaboration is not part of this pilot.

## Append-only results and decision log

Do not edit the predeclared sections above after observing results. Append
dated validation summaries, policy comparisons, revisions, and the final
decision below. Never remove or rewrite earlier entries.

<!-- Append observed results below this line. -->

### 2026-08-27 — first four-cell wave

Run commit: `203f42478717fd8f8c2dd65c6a521bc4e1c4f48c`. All four
self-contained bundles passed validation with no validation errors. Scores were
Qwen-P 3/6, GPT-P 2/6, Qwen-D 4/6, and GPT-D 3/6. P's score sum and virtual
union were 5/12 and 4/6; D's were 7/12 and 5/6. D used 146 calls, 977,567
tokens, $0.2042 recorded cost, and 7,905 seconds summed problem wall time,
versus P's 159 calls, 1,237,050 tokens, $0.2277, and 8,138 seconds.

The controller-generated `analysis.json` correctly recorded primary outcomes
but undercounted mechanism calls and outer timeouts because it relied on final
agent metadata, which is incomplete after worker timeouts. Post-run analysis-
only commit `f7d4a71a9aa620e6706d12d0bf324356c529a824` derives these counters
from immutable transcripts/results and adds explicit coverage fields. The raw
counts are 9 P planning calls (8 nonempty memos injected), 12 D restart calls,
and 7 outer agent timeouts. The original report and bundles remain unchanged;
the corrected report must be versioned separately with its analysis-code and
input hashes.

Mechanism inspection weakens a causal interpretation. Five of D's seven
successes, including two of its three pairwise-unique wins over P, occurred
without restart. Its two restart-path successes occurred five ordinary repair
calls after the second restart, and GPT's second restart exactly repeated a
previous failed candidate on all three GPT problems where restart fired. P's
strongest valid planning trace corrected Qwen's wrong numeric answer on
`p07_least_divisible`, but D also solved that problem. P's only pairwise-unique
success, GPT `p10_factorial_pow`, had a null planning `content` response and no
memo was injected, so it is not mechanism-aligned P evidence.

Decision: provisionally select D as the standalone performance-layer winner
because it wins in the same direction on both models, has the larger union,
and uses fewer realized resources. This is a tournament selection, not evidence
that diversified restart caused uplift. Do not run P+D: the preregistered gate
for credible unique, mechanism-aligned P and D successes is not met. Do not
repeat the wave as an integrity repair: primary evidence is valid, reporting is
recoverable from raw logs, and a post-outcome rerun would add selection bias.
Confirmation must compare D with a contemporaneous matched no-uplift/H control
before making an uplift claim.
