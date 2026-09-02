# Salvage and compiler-grounded progress packets: development plan

## Status and scope

This document is a plan, not launch authority. Recording it on
`online-development-v1` does not start, stop, retry, or alter any experiment.
The human-directed Stage 3 wave continues from its detached worktree at commit
`2e157547` and is isolated from this checkout. Implementation should begin on a
new `salvage-progress-packets-v1` branch created from the commit that records
this plan and the completed current-wave evidence.

The objective is to test the report's strongest recommendation before active
development ends:

> Preserve what Lean accepts, replace failing proof regions with explicit
> holes, attack the residual goals, and share only that compiler-grounded
> progress across model tracks.

The final candidate must remain a simple, problem-agnostic agent that runs via
the provided `python run.py` entry point. Development results are descriptive
and underpowered for small score effects. Promotion requires a functioning and
traceable mechanism, not a narrow aggregate lead.

## Starting evidence

The repaired scheduler changed the interpretation of the old audit:

- In the pre-audit core, C1 produced 18 packets and C2 produced 144, but none
  was consumed.
- In the currently collected repaired core, C1 consumed every generated
  packet and C2 consumed most generated packets. Exposure is therefore real
  now, although repeated C2 packets can become stale.
- In the first 25 collected matched C1/C2 blocks, C1 passed 16 and C2 passed
  15. C2 used more calls, money, and packet traffic without a demonstrated
  score advantage.
- Several accepted attempts had a packet in context, but there is not yet a
  verified solve attributable to peer information under the full causal
  criterion.

Consequently, event-driven delivery is no longer assumed to be a prerequisite.
Packet content is tested first on the repaired scheduler. Delivery timing is a
separate ablation if progress packets prove useful.

## Experimental invariants

### Condition boundary

All within-track proof search belongs in the control. Communication conditions
inherit that machinery unchanged and differ only at the cross-track boundary.

| ID | Within-track behavior | Cross-track behavior |
| --- | --- | --- |
| `B0` | Current repaired proof search | None |
| `C0+` | Sorrification, residual-goal repair, own verified helpers, and any separately promoted restart policy | None |
| `C1-failed` | Identical to C0+ | Current one-time failed-candidate packet |
| `C1-progress` | Identical to C0+ | One-time compiling-skeleton and residual-goal packet |
| `C1-progress-event` | Identical to C0+ | Event-driven, latest-wins progress packets |
| `C1-asym` | Identical base self-repair | Specialist-to-breadth skeleton/diagnosis treatment |
| `Self-MoA` | Separate secondary control | No communication; budget concentrated on the better solo model |

Specifically:

- C0+ may reuse each track's own skeletons, goals, and helper declarations.
- C0+ may not inspect the peer's candidate, diagnostics, skeleton, helper
  declarations, timing, or success state.
- A helper pool spanning both tracks is communication and must be a separate
  treatment.
- If a depth cap or restart policy is promoted, it must be identical in C0+
  and every communicating arm.
- `C1-failed` and `C1-progress` use the same delivery cadence when isolating
  packet content.
- `C1-progress` and `C1-progress-event` use the same payload when isolating
  delivery timing.

### Evaluator compatibility

Every online stage preserves:

- `python run.py` and the submission factory;
- the two allowed model identities and explicit medium reasoning effort;
- the pinned Lean environment;
- ledger, checkpoint, timeout, and verification-reserve behavior;
- exact problem files and declarations;
- final fresh Comparator authority.

A file containing `sorry`, `admit`, an axiom, or another escape is internal
partial state only. It must never:

- trigger fresh Comparator as a promising complete proposal;
- become the admissible submission checkpoint;
- stop a run as successful; or
- replace the best known complete no-sorry checkpoint.

## Proposed implementation

### 1. Offline causal-funnel analyzer

Extend analysis over stored transcripts to report, by problem, seed, condition,
and direction:

1. packet produced;
2. packet placed in a prompt before the recipient exhausted its calls;
3. recipient request completed with the packet;
4. recipient candidate changed in a way traceable to packet material;
5. borrowed material survived a warm Lean check;
6. borrowed material appeared in the final Comparator-passing file while the
   matched C0 cell did not solve;
7. paired outcome exceeded independent sampling at matched calls and dollars.

Stages 1-5 are mechanism evidence. Stage 6 is per-cell causal evidence. Stage
7 requires a later adequately powered evaluation and is not claimed from this
development ladder.

### 2. Conservative sorrifier

On a warm-Lean failure:

1. Parse diagnostic line ranges and identify the containing tactic block or
   `have` body.
2. Replace the smallest safe failing region with `sorry`.
3. Re-run warm Lean.
4. If it does not compile, conservatively widen the replacement or fall back
   to the ordinary failed candidate. Do not guess that a skeleton is valid.
5. If it compiles, obtain residual goal context from sorry diagnostics or a
   bounded `trace_state` follow-up.
6. Try the existing deterministic tactic cascade on each localized hole before
   spending another model call.
7. Store the compiling skeleton as untrusted partial state, separately from
   the admissible checkpoint.

Record at least:

- salvage attempted and reason;
- diagnostic and parent-candidate hashes;
- selected source span;
- skeleton hash;
- warm-check result and duration;
- retained lines/characters;
- residual-hole count and goal excerpts;
- deterministic hole attempts and outcomes;
- fallback reason.

Nested blocks, statement elaboration failures, and malformed declarations must
fail closed to the current repair path.

### 3. Within-track residual repair

When a track owns a compiling skeleton, its next repair prompt contains the
skeleton and localized residual goals and asks it to preserve verified
structure and fill the holes. It does not receive the peer's state in C0+.

Progress is measured by decreasing residual holes and preserving compiled
material, not by model confidence. A repeated skeleton or unchanged residual
signature is a stagnation signal.

### 4. Progress-packet strategy

A progress packet contains only:

- the bounded compiling skeleton;
- residual goals;
- compiling helper declarations or in-file `have` blocks with their necessary
  local context;
- one line of source model, attempt, check, and hash provenance.

It does not contain a broad critique, confidence score, or an unbounded failed
candidate. Initial packet delivery uses the repaired C1 one-time cadence so
payload quality can be compared without changing timing.

### 5. Optional delivery and role treatments

Only after progress-packet content shows useful reuse:

- test an event-driven single-slot latest-wins queue;
- measure actual delivery call and time rather than assuming exposure failure;
- add a 3-4-call fast-track reserve only if packets otherwise arrive too late;
- if a reserve is tested, include a matched idle-reserve control;
- test asymmetric sketch-and-fill only if solo data supports a meaningful
  breadth/specialist assignment.

The current repeated C2 whole-failure exchange is not a promotion candidate.

## Staged evaluation ladder

No stage advances automatically. Each stage produces a frozen manifest,
streaming status, artifacts, a short analysis, and an explicit human decision.

### Stage 0A: complete current-wave audit

**Online calls:** 0  
**Paid model cost:** $0

After the existing wave finishes and is collected, freeze its artifact index
and run the causal-funnel analyzer over all completed C1/C2 cells. Report:

- score and paired discordances;
- production and consumption by direction;
- delivery call distribution;
- packet-exposed accepted attempts;
- exact and approximate borrowed spans;
- stale and unconsumed packets;
- calls, cost, wall time, 429s, and verification failures.

This closes the historical exposure question before new behavior is added.

### Stage 0B: offline salvage replay

**Online calls:** 0  
**Paid model cost:** $0  
**Compute:** local/stored candidates plus warm Lean only

Run the sorrifier against stored failed candidates from the repaired wave.
Stratify by problem, model, error class, attempt phase, and whether the eventual
cell passed. Measure:

- eligible-failure count;
- compiling-skeleton yield;
- retained source fraction;
- residual holes and goal extraction success;
- deterministic tactic-cascade closures;
- additional warm-check latency;
- statement/elaboration/nesting failure categories.

Gate: continue only if the implementation safely creates meaningful compiling
skeletons on actual failures. A low overall rate can still qualify if a clear,
common error class is reliably salvageable. Never broaden source rewriting
merely to raise the rate.

### Stage 1A: deterministic safety canaries

**Online calls:** 0  
**Paid model cost:** $0

Add unit and real-Lean canaries for:

- top-level tactic failure;
- nested `have` failure;
- multiple goals;
- statement/type elaboration failure;
- malformed or out-of-range diagnostics;
- repeated unchanged skeleton;
- deterministic hole closure;
- partial state at deadline;
- recovery of the last complete checkpoint;
- prohibition on Comparator/checkpoint success for sorry-containing files;
- exact `python run.py` and judge-check compatibility after a hole is filled.

Gate: every safety invariant passes. Unknown syntax or state fails closed.

### Stage 1B: paid counterfactual packet replay

**Execution:** recorded repair states; warm Lean on completions  
**Initial paid tranche:** at most 12 balanced states x 3 payloads x K=2 = 72
model calls  
**Expansion:** K=8 only for preregistered informative states  
**Total cost cap:** set in the launch manifest, initially no more than $15

For the same recorded recipient state, construct:

1. no packet;
2. current failed-candidate packet;
3. compiler-grounded progress packet.

Balance target model, direction, problem, and error class. Use temperature 0.2
and identical seeds/call parameters. Stream warm-pass, error count, hole count,
structural reuse, tokens, latency, and cost after each matched state.

Gate:

- If current packets match or beat progress packets, retain the current
  payload and do not promote the exchange half of salvage.
- If neither packet beats no-packet repair mechanistically, retain within-track
  salvage but stop peer-packet work.
- If automatic skeleton yield is poor, cheaply probe direct specialist-created
  sketch-and-fill before investing further in the sorrifier.

### Stage 2A: within-track salvage microcells

**Conditions:** B0 versus C0+  
**Problems:** 4 informative problems selected from Stage 0  
**Replications:** 1 matched seed initially  
**Calls:** approximately 4-6 per model per cell  
**Maximum cells:** 8 initially

Run the exact evaluator-facing path. Primary evidence is whether salvage is
invoked, skeletons compile, holes decrease, and complete proofs emerge without
losing the best admissible checkpoint. Scores are descriptive.

If a chain-depth/structural-restart change is desired, test it as a separate
C0+-only arm here. Promote it into the common base only after its own recorded
ablation; do not silently bundle it with salvage.

### Stage 2B: packet-content microcells

**Default conditions:** C0+, C1-failed, C1-progress  
**Problems:** 6 diagnostic problems  
**Replications:** 1 matched seed, followed by targeted repeats  
**Calls:** approximately 4-6 per model per cell  
**Maximum initial cells:** 18

Provisional diagnostic set:

- `p07_least_divisible`
- `p08_sum_products`
- `p09_imo1964`
- `p10_factorial_pow`
- `putnam_2020_a2`
- `rmo_2000_2`

Stage 0 may replace a member when the final current-wave evidence shows that it
does not exercise repair or salvage.

Gate: C1-progress is collaboration-promising only if packets are consumed and
their compiler-grounded material is reused and survives Lean. Strong promotion
evidence is at least one Comparator-passing peer contribution absent from the
matched C0+ proof trajectory. A small aggregate lead without this trace is
inconclusive.

Stage 1B may justify dropping C1-failed from online cells, but its replay
evidence remains part of the final ablation story.

### Stage 2C: selected alternatives

Run only alternatives still justified by prior evidence:

- C1-progress versus C1-progress-event to isolate delivery timing;
- symmetric progress packets versus C1-asym to isolate directional diagnosis;
- C0+ versus Self-MoA to test whether two models are justified;
- verified cross-track helper pool off versus on.

Do not run a broad grid. Each comparison gets one hypothesis, a matched control,
and a mechanism trace. If Self-MoA wins clearly, the final design should become
a cascade or single-model portfolio rather than forced collaboration.

### Stage 3A: expanded-core breadth, one seed

**Conditions:** selected practical pair, normally C0+ and C1-progress  
**Problems:** 11  
**Replications:** 1 matched seed  
**Calls:** full 25-call-per-model ceiling  
**Cells:** 22

Exclude only the currently obvious/evaluator-trivial problems:

- `p01_linear`
- `p02_frac_cancel`
- `p03_sq_ge_two_ab`
- `p04_sum_sq`
- `p05_gcd_mersenne`

Expanded core:

- `p06_pow_mod`
- `p07_least_divisible`
- `p08_sum_products`
- `p09_imo1964`
- `p10_factorial_pow`
- `putnam_2018_a1`
- `putnam_2020_a2`
- `rmo_2000_2`
- `rmo_2000_3`
- `rmo_2000_6`
- `rmo_2001_2`

Stream per-block results, calls, skeleton traces, packet funnel, and exact final
verification. Inspect the first several blocks before authorizing replication.

### Stage 3B: matched replication

**Additional replications:** up to 2  
**Maximum total:** 11 problems x 3 seeds x 2 conditions = 66 cells

Advance only when Stage 3A shows a sound measurement path and the intended
mechanism actually occurs. Report paired problem-seed differences, exact
intervals, mechanism exposure, and resource use. Do not claim that a one- or
two-problem difference establishes uplift.

### Stage 4: final compatibility rehearsal

Before selecting the submission design:

- place exactly the intended design in the default factory;
- run the published command and `scripts/judge_check.sh` from a fresh checkout;
- verify the protected entry point, model identities, medium reasoning,
  accounting, checkpoint recovery, timeout behavior, and fresh Comparator;
- run a bounded all-16 development-set rehearsal only if it supplies missing
  compatibility evidence;
- export the candidate as a small reviewable diff from the recorded base.

No development result substitutes for a sealed holdout or official evaluation.

## Online execution discipline

- Do not touch or reuse the current Stage 3 worktree, result root, controller,
  workers, containers, or task IDs.
- Recheck worker availability immediately before every authorized launch.
- Worker 10 remains excluded from evaluator cells.
- Interleave arms within problem-seed blocks so endpoint period effects and
  429s do not align with condition.
- Admit requests at a conservative measured provider concurrency; idle workers
  are not a reason to exceed endpoint capacity.
- Use fresh namespaced checkouts and result roots for every stage.
- Never retry a possibly running paid cell without remote reconciliation.
- Continuously publish preliminary terminal results and transcripts; do not
  wait for an entire wave to learn that the mechanism is absent.
- Record logical calls, physical requests, cost-free retries, cost, wall time,
  warm checks, Comparator checks, and accounting completeness.

## Planned commit structure

Keep the implementation recoverable and auditable:

1. Plan, literature report, and frozen current-wave analysis.
2. Analysis-only packet funnel and counterfactual-state extraction.
3. Conservative sorrifier, partial-state type, and offline replay tests.
4. Within-track residual repair and C0+ configuration.
5. Progress-packet payload and C1-progress configuration.
6. Optional delivery/asymmetric/helper-pool treatments, each in its own commit.
7. Stage manifests, results summaries, methods snapshot, and final selection.

Behavior-neutral instrumentation is applied identically to every arm. Any
change that can alter proof search, information, timing, or call allocation is
an explicit treatment or separately promoted common-base change.

## Stop and decision rules

Stop or fall back when:

- sorrification cannot reliably create meaningful compiling skeletons;
- goal extraction is brittle or unsafe;
- sorry-containing state can reach final acceptance or overwrite a complete
  checkpoint;
- models routinely discard the skeleton and no localized progress is visible;
- packet content is not reused or does not survive Lean;
- added warm checks consume verification reserve or harm timeout recovery;
- the practical independent control matches or beats communication without a
  traceable peer contribution;
- Self-MoA makes the second model unjustifiable; or
- implementation complexity exceeds the evidence available before the
  development deadline.

Positive development evidence supports only the statement that the mechanism
is working, interpretable, compatible, and promising enough for a later proper
evaluation.
