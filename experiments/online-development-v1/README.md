# Online development v1

> **Infrastructure allocation:** workers 8--9 are human-directed only and
> worker 10 is the machine-controlled coordinator. Automated cells use only
> workers 1--7. See [WORKER_ALLOCATION.md](WORKER_ALLOCATION.md).

This prospective development line starts from corrected-challenge commit
`e1c8fee`. It does not modify C0/C1/C2 strategy definitions. Its first revision
changes only shared candidate-safety, verification, state, and deadline
infrastructure.

The preregistered Stage 3 replication is defined in
`stage3-replication-v1.json`. It repeats the pre-audit shallow format on the
current substrate: three replications of each condition on the six-problem
core and one replication on each of the ten remaining corrected problems. The
84 cells run as 28 matched C0/C1/C2 blocks across three independent worker
trios. This experiment-specific use of workers 1--9 was explicitly authorized;
worker 10 remains excluded.

The writeup-ready methods snapshot for this wave is in `METHODS.md`. Stage 3
and later experiment waves should commit a wave-local methods snapshot beside
their frozen plan before or during execution. The snapshot must identify the
exact source commit under test, dataset and replication structure, conditions,
shared substrate, resources, verification path, outcomes, and limitations.
Later mechanism revisions receive a new experiment version and methods
snapshot rather than silently rewriting the historical document.

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

### First provisional-success deployment canary

The first three-host launch from `425a5c8` made zero provider requests. A Git
archive correctly omitted the untracked `.env`, but the online launcher had no
secret preflight. The agent then counted six local missing-key failures as
dispatched and physical calls before ordinary final verification. These are
configuration canaries, not scientific results.

The launcher now refuses a frozen checkout without a readable, nonempty
`OPENROUTER_API_KEY` before starting the harness. Provider-request counters are
maintained by the LLM client at the actual HTTP emission boundary; agent
metadata separately reports semantic calls attempted, logical provider calls,
and physical requests including retries. The secret is copied server-side from
the existing protected checkout and is never printed or added to Git. Relaunch
uses distinct `stage2g2r1-*` task IDs and preserves the failed artifacts.

### Provisional-success scientific canary

The three matched `stage2g2r1-*` cells completed with 16 provider responses,
zero 429 retries, zero structural rejections, and zero warm-Lean successes.
Consequently the event-driven fresh verifier made zero in-agent Comparator
calls, as intended. C0 and C1 received all six planned calls in 320.193 and
276.836 seconds. C2 received only four calls and hit the dispatch cutoff after
512.174 seconds. Its two Qwen calls took 25.1 and 13.0 seconds while the paired
GPT calls took 115.1 and 226.4 seconds. This is direct evidence that lockstep
suppresses treatment dosage and wastes fast-track capacity. The wave validates
the gate revision but is not used to estimate mechanism performance.

## Independent-track scheduler revision

Mechanism iteration remains paused. The shared scheduler now dispatches each
model's next repair as soon as that track's response and Lean check complete.
Observations retain per-track logical call numbers. The unchanged strategy is
invoked when both observations for a logical round exist; generated packets
are queued for the target's next not-yet-dispatched call rather than blocking
the fast track or overwriting an earlier pending packet.

Every packet event records its generation round, source, target, queue
position, and (when consumed) target call and round. This makes latency-induced
asymmetric exposure auditable. Metadata separates calls attempted, logical
provider calls, and physical HTTP requests. An outer cancellation cancels all
independently in-flight requests so deadline handling cannot leak background
spend. No larger online wave should run until this scheduler completes the
offline, pinned-image, and matched online ladder.

The offline non-Docker suite reports 95 passed and 8 skipped. Its sole failure
is the inherited frozen-manifest hash assertion: the corrected sample manifest
is intentionally different from the earlier solo experiment snapshot, so that
test must not be weakened or relabeled as a scheduler regression. Focused
scheduler tests report 37 passed, including fast-track advancement, queued
packet provenance, and cancellation of in-flight requests. In the pinned Lean
image, the independent scheduler exercised four real warm-REPL checks while a
deliberately delayed peer failed to block the fast track; the scheduler test
and the full worker fresh-verifier regression both passed in 79.28 seconds.

### Independent-scheduler scientific canary

The matched `stage2async1-*` cells completed cleanly with 16 fully accounted
provider responses, zero 429 retries, zero provider or harness errors, and zero
warm-Lean successes. C0/C1/C2 dispatched 5/6/5 calls. Every cell completed all
three Qwen calls; the previous lockstep C2 cell completed only two. Live events
showed Qwen calls 2 and 3 dispatching while the first GPT call remained in
flight. This is direct validation that independent scheduling restores
fast-track dosage.

The endpoint remained heavy-tailed. GPT latencies reached 342.8 seconds in C0
and 247.1 seconds in C2, causing those tracks to cross the unchanged dispatch
cutoff after GPT call 2. The HTTP client's read timeout is an inactivity limit,
not a total request deadline; cancelling an already dispatched paid call would
make spend uncertain under the current accounting contract. Thus the scheduler
fix prevents the tail from idling Qwen but cannot safely erase GPT tail latency.
Wall time is not a clean comparison across the two waves because provider
latency changed substantially.

Packet provenance also prevents a false mechanism interpretation. Qwen had
already exhausted its calls before GPT observations arrived. C1 generated two
packets, used one on GPT call 2, and left one queued for Qwen. C2 generated four,
used one on GPT call 2, and left three queued. Therefore the current reciprocal
strategies do not deliver reciprocal exposure under realistic latency skew.
This is a mechanism-design problem to address only after the remaining shared
substrate audit; it is not a reason to restore lockstep.

### Preliminary result visibility

Cold final Comparator remained a 89.7--114.5-second tail after the agent had
already atomically written its final checkpoint. The development launcher now
recognizes only a checkpoint containing complete `independent-track-v1`
metadata and emits a compact `preliminary-status.json` while the unchanged
Comparator continues. It reports request accounting, cutoff state, structural
rejections, warm and fresh-verified successes, and packet generated/used/pending
counts. It explicitly marks final judging as pending and cannot claim ultimate
pass status. The collector surfaces this preliminary record for running cells,
then replaces it with the ordinary final status once judging completes.

This shortens time-to-information without changing the agent, conditions,
worker, Comparator, or published evaluation command. Provisional recovery
checkpoints are ignored. Focused tests report 22 passed; the full non-Docker
suite reports 96 passed and 9 skipped, with only the already documented
intentional frozen-manifest mismatch failing.

### Qwen reasoning-control closure

Five of the nine Qwen calls in the independent-scheduler canary exhausted the
12,000-token completion ceiling. Two truncated before returning the required
theorem. A single paid replay used the exact worst archived repair prompt and
changed only `reasoning.effort` to `none`, which OpenRouter's live model
metadata permits for Qwen but not for GPT-OSS.

The archived control used 12,000 completion tokens, 68.374 seconds, and
$0.00329459, ending with `finish_reason=length` and no complete required
theorem. The probe used 3,828 tokens, 20.947 seconds, and $0.00117, ended with
`finish_reason=stop`, and returned a structurally complete theorem. Warm Lean
rejected the proof with four messages; this probe establishes output usability
and resource reduction, not proof quality. The shared v2 invocation now sends
`reasoning={"effort":"none"}` for Qwen in every condition and leaves mandatory
GPT-OSS reasoning unchanged. Raw probe events and candidate are preserved at
`/opt/takehome-qwen-reasoning-probe-r1`; the compact result is checked in as
`qwen-reasoning-probe-r1-results.json`.

After reviewing the first end-to-end reasoning-off base canary, the working
policy was deliberately changed to explicit medium reasoning for both Qwen and
GPT-OSS. This keeps reasoning effort matched across tracks and conditions for
the next mechanism comparisons. The reasoning-off canary remains a frozen
efficiency/quality diagnostic and must not be pooled with medium-reasoning
results. Medium parity is the current default, not a claim that an ablation has
established it as optimal.

Two end-to-end canaries close the integration loop. The superseded
reasoning-off C0 cell completed six accounted calls and final judging without a
harness error. Its three Qwen calls took 1.6--2.2 seconds and only 248--249
tokens, but the last two candidates were byte-identical and all failed Lean.
This is strong efficiency evidence and a warning against interpreting output
completeness as proof quality.

The current explicit-medium C0 cell requested `reasoning.effort=medium` from
both endpoints and completed through the full worker, preliminary checkpoint,
and final Comparator path. Qwen returned 3,557 tokens in 24.361 seconds; GPT-OSS
returned 9,946 tokens in 208.053 seconds. Both stopped normally, reached Lean,
and failed the hard problem. Both requests and $0.002647424 total spend were
fully accounted, with no provider, harness, cutoff, or Comparator timeout.
Reasoning-effort parity therefore does not imply latency or token parity. These
cells validate invocation and compatibility, not relative proof quality.
