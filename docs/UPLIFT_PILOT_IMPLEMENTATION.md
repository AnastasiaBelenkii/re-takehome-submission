# Uplift Pilot Implementation Handoff

## Objective

Implement a reproducible four-cell solo-agent pilot that selects one
within-model performance uplift policy before collaboration is studied.

This is an exploratory engineering tournament, not a confirmatory causal
study. Preserve simple, factorable policies and complete provenance. Do not
launch paid pilot runs as part of this implementation task; finish with local
tests and minimal smoke tests, then report the exact launch commands for human
review.

## Repository and safety constraints

- Read `RULES.md`, `docs/AGENT_API.md`, and the existing baseline and submission
  agents before editing.
- Preserve the existing independent-repair evidence agent and launcher.
- Work on a new descriptive branch from the current clean commit.
- Do not modify upstream harness behavior unless strictly necessary.
- Keep the judged submission independent of experiment infrastructure.
- Never write API keys or `.env` contents into artifacts, logs, manifests, or
  Git.
- Do not special-case any problem or encode sample-specific mathematical facts.
- Use pinned commits and detached worktrees for real runs.
- Failed and interrupted runs are artifacts; never overwrite them.

## Experimental design

The pilot has four solo cells, run concurrently on separate machines:

1. Qwen + P
2. GPT-OSS + P
3. Qwen + D
4. GPT-OSS + D

Models:

- `qwen/qwen3.5-flash-02-23`
- `openai/gpt-oss-120b`

Use one common uplift policy for both models when selecting the final `U*`.
Do not silently select model-specific policies.

### Common substrate H

Both policies receive only common diagnostic and provenance infrastructure:

- Bounded, deduplicated Lean diagnostics while preserving raw events
- Candidate hash and normalized error-signature recording
- Best-checkpoint preservation
- Call-ledger enforcement
- Complete per-attempt metadata

H may observe and record stagnation. Only D may react to it.

### Candidate P: adaptive planning/decomposition

Each solo model:

1. Makes a direct complete-Lean attempt.
2. After the first failed Lean check, spends exactly one model call producing a
   short structured strategy memo containing:
   - informal mathematical proof;
   - Lean proof architecture;
   - useful subgoals or intermediate lemmas;
   - likely tactics and Mathlib lemmas;
   - diagnosis of the failed attempt.
3. Generates a new complete Lean file conditioned on that memo.
4. Continues ordinary plan-conditioned repair.
5. Never uses diversified restart behavior.

The planning call counts against the 25-call ceiling and should request at most
approximately 2,500 output tokens. Planning text must never be submitted to
Lean as the candidate.

### Candidate D: diversified restart

Each solo model:

1. Makes a direct complete-Lean attempt.
2. Performs ordinary Lean-feedback repair.
3. Detects stagnation using explicit, logged rules:
   - an exactly repeated normalized candidate triggers immediately; or
   - a repeated normalized error signature/no meaningful diagnostic progress
     must persist across at least two transitions.
4. On stagnation, abandons the active trajectory and starts from the pristine
   theorem, carrying only a concise bounded record of failed approaches.
5. Requires a materially different mathematical or Lean strategy.
6. Permits at most two diversified restarts.
7. Never uses a separate natural-language planning call.

Preserve the best checkpoint when a restart produces a worse candidate.

## Pilot problem set and resource envelope

Use exactly these six problems:

- `p03_sq_ge_two_ab`
- `p06_pow_mod`
- `p07_least_divisible`
- `p10_factorial_pow`
- `putnam_2020_a2`
- `rmo_2000_6`

For every cell:

- 20 minutes outer wall time per problem
- 18 minutes available to the agent after verification reserve
- `$1.00` maximum per problem
- 25 maximum dispatched model calls per problem
- Planning, diagnosis, proof generation, repair, restart, failed calls, and
  cancelled calls all count
- Proof generation/repair maximum output: 12,000 tokens
- Planning maximum output: approximately 2,500 tokens
- Temperature: 0.2 unless existing baseline configuration establishes a
  different shared value
- Two outer problem workers per machine
- Same Lean image digest and verification settings
- No machine crossover for this exploratory pilot

Maximum calls are matched; realized calls, tokens, spend, and wall time may
differ because of early success and external limits. Record all of them.

The 20-minute limit matches the existing control and the planned full
confirmation regime, but remains an intentionally abbreviated research
condition rather than the eight-hour private-holdout judging limit. With six
problems, two outer workers per machine, and all four cells running concurrently,
the pilot has three worst-case waves and should take approximately 60 minutes.
Do not add a large pre-deadline drain buffer merely to obtain cleaner accounting
statuses. Use the same deadline and cancellation behavior in all four cells. A
request cancelled at the agent deadline may correctly make budget accounting
incomplete and produce `cost_unknown`; count that problem as unsolved, preserve
its preceding evidence, and treat its recorded spend as a lower bound rather
than invalidating the run.

## Checked-in experiment contract

Create:

```text
experiments/
└── uplift-pilot-v1/
    ├── README.md
    ├── problems.txt
    ├── conditions/
    │   ├── qwen-p.json
    │   ├── gpt-p.json
    │   ├── qwen-d.json
    │   └── gpt-d.json
    └── runs.jsonl
```

The README must predeclare the hypothesis, policies, resource envelope,
selection rule, and revision rule. Condition files are authoritative static
inputs. Do not put timestamps, resolved commits, hostnames, secrets, or output
paths in them.

Implement one generic launcher that accepts a condition manifest. It must:

1. Refuse tracked or untracked source changes, except explicitly ignored
   runtime files.
2. Resolve and record the exact Git commit.
3. Create a uniquely named detached worktree and result directory.
4. copy the runtime `.env` into the worktree with mode 0600 without copying it
   into results.
5. Verify the declared design ID and model before launch.
6. Materialize one effective configuration used both for provenance and the
   actual process environment; do not duplicate configuration literals.
7. Record the manifest hash, problem-list hash, launcher hash, Lean image
   digest, host metadata, exact command, and effective settings before launch.
8. Refuse to reuse or overwrite a run directory.
9. Print the PID, commit, worktree, run root, log, provenance, and monitoring
   commands.
10. Support a non-mutating `--check` mode.

Each result bundle should contain:

```text
<condition>-<UTC>-<short-sha>/
├── provenance.json
├── condition.json
├── run.log
├── run.pid
└── outputs/
```

## Collection and validation

Implement a simple collector that uses `rsync --partial` to copy self-contained
run bundles from workers to a central archive. It must not mutate remote runs or
require a shared database/filesystem.

Implement a validator that checks:

- All declared conditions and exactly six declared problems are present
- `finished_at` is non-null for completed runs
- No problem is `missing`
- The model used matches the condition
- Commit, design ID, manifest hash, problem-list hash, and effective limits
  match expectations
- Events, transcripts, results, and summaries exist and agree
- Calls do not exceed the declared ceiling
- No apparent API key is present
- Final artifact checksums can be generated

The validator should emit compact JSON plus a human-readable table/report. A
run is not evidence until validation succeeds. Invalid runs remain preserved
with an explicit reason.

`cost_unknown`, timeout, proof failure, model error, and zero score are valid
completed pilot outcomes when their artifacts and provenance are complete.
Report their incidence and causes. Do not make validation success depend on a
proof passing or on exact cost being available after an in-flight cancellation.

## Experiment ledger

Use `runs.jsonl` as an append-only index of collected runs. Store identifiers,
condition, commit, host, timestamps, status, validation result, score, cost,
and artifact path. Do not store complete transcripts in the ledger.

The experiment README should have an append-only results/decision section. Do
not rewrite the predeclared design after observing results.

## Selection and revision rules

For P and D calculate:

- Each model's solo score
- Sum of solo scores
- Virtual Qwen-or-GPT problem union
- Per-problem complementarity
- Calls, tokens, cost, wall time, timeouts, and stagnation behavior

Promote a clear standalone winner. Prefer the simpler policy when effectively
tied. Test P+D only if P and D have credible unique successes aligned with
their intended mechanisms. P+D receives the same 25-call ceiling and must beat,
not tie, the standalone leader.

Permit at most one generic revision, only when the same failure appears on at
least two problems and the change contains no problem-specific information.

After selection, freeze `U*` and later confirm it using the actual independent
two-model portfolio on all 16 problems at the full 20-minute regime.

## Collaboration boundary

Do not implement collaboration in this task. Keep the single-model uplift
policy independent of any peer state. The later collaboration layer will
control only which candidate/diagnostic packet crosses between two otherwise
unchanged uplift state machines.

Do not change the existing independent-portfolio scheduler or rerun that
control as part of this task. Round synchronization and asynchronous
cross-model checking are irrelevant to these four solo pilot cells and will be
decided when the collaboration comparison is specified.

The leading later treatment is one symmetric reciprocal cross-repair exchange,
with no extra model calls. Do not bake that behavior into H, P, or D.

## Required tests

Use fake LLM and Lean services following the existing test style.

P tests:

- Planning fires exactly once and only after the first failed Lean candidate
- Planning consumes one call
- Planning output is never Lean-checked
- No D restart path is reachable
- Call ceiling is enforced

D tests:

- Exact candidate repetition triggers restart
- A single similar error does not restart prematurely
- Persistent unchanged errors trigger the logged restart
- Restart begins from the pristine theorem with bounded failure memory
- At most two restarts occur
- Best checkpoint survives later regressions
- No P planning path is reachable
- Call ceiling is enforced

Infrastructure tests:

- Manifest validation rejects unknown keys and invalid combinations
- Effective configuration is identical to recorded provenance
- Dirty-tree and existing-directory launch refusals work
- Validator detects missing problems, wrong model, wrong commit, mismatched
  limits, excess calls, unfinished runs, and leaked-secret patterns
- Existing submission-agent and judge tests continue to pass

## Completion criteria

Before reporting completion:

1. Run focused unit tests.
2. Run the existing full test suite.
3. Run launcher `--check` for all four conditions.
4. Run minimal fake or deliberately shallow smoke tests for P and D without
   launching the paid six-problem pilot.
5. Review `git diff` for secrets, sample-specific logic, duplicated settings,
   and unnecessary framework complexity.
6. Report files changed, tests run, remaining risks, exact condition commits,
   and the four commands that would launch the real pilot.

Do not start the real pilot until the human explicitly approves those commands.
