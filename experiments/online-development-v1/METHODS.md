# Methods: online-development-v1 Stage 3

## Task and evaluation setting

We developed a problem-agnostic agent that uses two fixed language models,
`qwen/qwen3.5-flash-02-23` (Qwen) and `openai/gpt-oss-120b` (GPT-OSS), to
produce complete Lean 4 proofs. Each input contains an English problem and a
Lean file whose declarations contain proof holes. A trial scores as successful
only when the returned file passes the same pinned Lean Comparator used for
evaluation. All model calls were made through OpenRouter. No external tools or
services were available to the agent at run time other than the supplied model
and Lean interfaces.

The present experiment studies a deliberately narrow collaboration mechanism:
whether exchanging a peer model's failed candidate and compiler diagnostics
improves a common two-model proof-search portfolio. It is a development study
on the 16 public sample problems, not an estimate of private-holdout accuracy.
The tested C1 and C2 mechanisms are frozen experimental conditions and should
not be read as a commitment to the final submitted collaboration policy.

## Common proof-search substrate

All three experimental conditions use the same solver, prompts, models,
sampling parameters, scheduling policy, proof checks, and resource limits. The
only intended treatment difference is peer-packet cadence.

Before making a model call, the solver applies a generic deterministic tactic
cascade (`omega`, `norm_num`, `nlinarith`, `linarith`, `ring`, `aesop`, and
`simp_all`) to every proof hole. A successful deterministic candidate is
verified and returned identically in every condition. Otherwise, Qwen and
GPT-OSS begin independent repair tracks from the pristine challenge. Each
track receives the problem statement, its current complete Lean candidate,
bounded Lean diagnostics, and bounded memory of abandoned approaches. A track
is restarted from the pristine challenge, at most twice, after repeating a
normalized candidate or sustaining the same error signature. Restarts ask for
a materially different mathematical or Lean strategy.

The two tracks are scheduled asynchronously. As soon as one model response has
been checked, that track may issue its next request without waiting for the
other model. This removes the wall-time amplification caused by the earlier
lockstep scheduler while retaining independently numbered observations for
the packet treatment. Search terminates when either track produces a candidate
that passes fresh verification. If no candidate succeeds, the solver returns
the highest-ranked admissible checkpoint rather than a gate-rejected response.

Both models use temperature 0.2, a maximum of 12,000 generated tokens per
request, the same cell-level seed, and medium reasoning effort. Each track may
make at most 25 semantic calls. The prompt requests a complete Lean file using
`Mathlib`, preservation of all required declarations and numeric answers, no
unsafe escapes, and a short proof sketch before a new proof. These parameters
are held constant across C0, C1, and C2.

## Collaboration conditions

Each problem-seed block contains three matched conditions:

- **C0 (no communication):** Qwen and GPT-OSS search independently and no
  information crosses tracks.
- **C1 (one reciprocal exchange):** after the first same-numbered round in
  which both tracks have failed, each model receives one packet derived from
  the other model's failed candidate and Lean diagnostics.
- **C2 (repeated reciprocal exchange):** the same reciprocal exchange occurs
  after every eligible same-numbered dual-failure round.

Packets contain bounded excerpts of the peer's candidate and compiler
diagnostics, up to 6,000 characters. A generated packet is queued for the
recipient's next request; packet generation does not block a faster track or
add model calls. The recipient is explicitly instructed to evaluate the
evidence critically and reuse only useful material. Packet generation,
queuing, consumption, source model, target model, and the exact attempt that
consumed a packet are recorded. This permits a distinction between nominal
assignment to a collaboration condition, actual exposure to peer information,
and a successful proof generated on a packet-exposed attempt.

C0 is not a single-model baseline: it is a two-model portfolio without
communication. Consequently, C1−C0 and C2−C0 estimate the effect of the
packet mechanism conditional on running both model tracks. Qwen-solo and
GPT-OSS-solo results are analyzed separately to address whether the complete
two-model system improves on either model alone. Historical solo runs used the
provided single-model agent with up to 25 turns, temperature 0.2, and 12,000
maximum output tokens. Because the shared substrate and corrected problem set
changed during development, results from incompatible solver revisions are
reported as contextual baselines rather than pooled as exchangeable trials.

## Candidate safety and proof verification

The initial implementation rejected candidates by textual equality of Lean
declaration headers. Audit replay and online microcells showed that this rule
rejected semantically harmless changes in qualification, binder spelling, and
whitespace. The current solver therefore uses only a cheap structural guard
before Lean: every required declaration name must occur exactly once with a
compatible declaration kind. Additional fresh helper declarations are
allowed, and imports are normalized deterministically to `import Mathlib`.
The structural guard is a completeness filter, not an assertion of theorem
equivalence.

Every structurally admissible proposal is checked in the warm Lean service.
A warm success is only provisional. Before it can stop search or become a
trusted checkpoint, it must pass numeric-answer-shape checks and a fresh
Comparator invocation in a separately scoped container. The runner performs
a second fresh Comparator check on the final returned file. Failed or rejected
proposals remain transcript records but cannot overwrite trusted state or
supply packet source code unless they passed the structural guard. This design
uses the evaluator, rather than source-text heuristics, as the authority on
statement preservation and proof validity.

## Problem set and experimental design

The corrected public set contains all 16 supplied problems. We preregistered a
six-problem core (`p03_sq_ge_two_ab`, `p06_pow_mod`, `p07_least_divisible`,
`p10_factorial_pow`, `putnam_2020_a2`, and `rmo_2000_2`) and evaluated each
condition at seeds 1729, 2718, and 3141. The remaining ten problems form a
single-seed breadth set: `p01_linear`, `p02_frac_cancel`, `p04_sum_sq`,
`p05_gcd_mersenne`, `p08_sum_products`, `p09_imo1964`, `rmo_2000_6`,
`rmo_2001_2`, `rmo_2000_3`, and `putnam_2018_a1`. The breadth label denotes
replication depth rather than difficulty; it includes several of the hardest
observed problems.

This yields 84 cells: 6 core problems × 3 seeds × 3 conditions plus 10
breadth problems × 1 seed × 3 conditions. Conditions for a problem-seed
block run concurrently on a matched trio of workers. Three worker trios permit
up to nine simultaneous cells, and condition-to-worker assignment rotates
across blocks to reduce confounding by machine or provider timing. Each worker
runs an immutable checkout of commit
`2e15754721414db00780a15fbce4d27d2c1f407c`. Worker 10 is excluded from the
study.

Two upstream dataset corrections are included. The stated second minimum in
`rmo_2000_6` is corrected from 20 to 10, and the Putnam answer sets are inlined
so that a candidate cannot prove a result circularly by redefining the named
answer object. These corrected tasks are not numerically pooled with outcomes
from their defective versions.

## Resource envelope and failure handling

Each cell has a $1 OpenRouter cap and a 28-minute outer limit. New requests may
be dispatched for the first 16 minutes; the remainder is reserved for
in-flight responses, Lean checks, serialization, and final verification. Warm
Lean checks have a 120-second timeout and Comparator checks a 180-second
timeout. At most two retries are allowed only for explicitly typed 429
responses known to have incurred no cost. Provider failures with uncertain
spend close the ledger and remain failures rather than being automatically
rerun. Experimental outcomes are classified from result artifacts, not merely
from process exit codes.

## Outcomes and analysis

The primary outcome is intention-to-treat proof success for each matched
problem-seed-condition cell, defined by the final fresh Comparator verdict.
Primary descriptive contrasts are paired C1−C0, C2−C0, and C2−C1 changes
in pass outcome. Given the small and heterogeneous public set, differences are
reported per problem and as descriptive aggregates rather than treated as a
precise estimate of holdout uplift.

Secondary outcomes include semantic and physical request counts, model and
attempt producing the accepted proof, cost, tokens, wall time, provider
latency, timeouts, rate-limit retries, restarts, error-signature changes, and
accounting completeness. For collaboration arms we additionally report packet
generation and consumption, whether success occurred before or after
communication, and whether the accepted attempt directly consumed a peer
packet. A condition-level score difference without packet exposure is not
interpreted as evidence for the proposed mechanism. Conversely, a
packet-exposed success is treated as mechanistic trace evidence, not by itself
as a causal estimate; matched replication and per-problem counterfactual
outcomes remain necessary.

The experiment is analyzed from immutable transcripts, event logs,
checkpoints, usage records, final solutions, and independent Comparator
verdicts. Results are reported as they complete for time-to-information, but
the frozen 84-cell matrix and intention-to-treat denominator are retained.
Mechanism redesigns prompted by these results will be assigned new condition
names and a new experiment version rather than silently modifying C1 or C2.
