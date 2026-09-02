# Stage 3: matched hard-problem restart cell

## Design

This stage tested C0+ against C1+ on `putnam_2020_a2`, selected because the
problem was unsaturated in prior results and had high offline salvage yield.
Three matched seed blocks ran concurrently:

| Replication | Seed | C0+ worker | C1+ worker |
| ---: | ---: | --- | --- |
| 1 | 1729 | 1 | 2 |
| 2 | 2718 | 3 | 8 |
| 3 | 3141 | 9 | 4 |

The exact agent code was
`36da50f75e1d215ff73be8c76081081f8553b44f`. Each cell used four calls per
model, a $0.25 cap, 1,200-second outer limit, 720-second dispatch cutoff,
180-second Comparator timeout, two-second salvage checks, and a 420-second
semantic model-call deadline. All first-round request bodies were byte-identical
within each matched seed/model pair.

## Outcomes

| Arm | Solves | Calls | Useful skeletons | Mean wall s | Total spend |
| --- | ---: | ---: | ---: | ---: | ---: |
| C0+ | 0/3 | 24 | 4 | 558.342 | $0.038691044 |
| C1+ | 0/3 | 24 | 2 | 550.387 | $0.035580383 |

All six cells completed within time and budget with complete cost accounting.
Final Comparator completed without timing out in every cell. There is no score
uplift in this stage.

Provider responses diverged despite matched seeds and byte-identical first
requests. Thus paired seeds do not make the hosted endpoints deterministic;
transcript/mechanism evidence remains necessary for interpreting small waves.

## Salvage and packet mechanism

Six compiler-grounded partial skeletons were produced across 48 total model
calls: four in C0+ and two in C1+. This confirms that within-track salvage also
operates on the harder problem, but no trajectory reached a complete proof.

Only seed 3141 C1+ produced peer packets:

- GPT call 1 yielded a compiling one-line retained skeleton.
- That packet was delivered to Qwen call 3.
- The packet-exposed Qwen response did not compile or salvage and produced 22
  diagnostics, beginning with an unavailable `Finset.Icc_eq_range` constant.
- GPT call 4 later yielded a compiling four-line retained skeleton and generated
  a newer packet, but Qwen had exhausted its calls before consuming it.

In total C1+ generated two packets, consumed one, and ended with one pending.
The only packet-exposed response did not improve compiler-grounded state. This
is evidence that the current cross-track mechanism is legible and operational,
but not evidence that it helps on this problem.

## Concurrency and latency

The six cells launched together, creating up to twelve simultaneous initial
model requests. Both models returned all 24 requests:

| Model | Responses | Mean latency | Maximum latency |
| --- | ---: | ---: | ---: |
| Qwen 3.5 Flash | 24 | 38.8 s | 70.6 s |
| GPT-OSS 120B | 24 | 103.0 s | 399.5 s |

There were zero HTTP 429s, request errors, semantic-deadline cancellations, or
unknown-cost reservations. This wave does not support a hard low-concurrency
Qwen limit. Its long wall-time tail came from GPT-OSS latency and final cold
Comparator runs, not Qwen refusal. The 420-second semantic deadline bounded the
observed GPT tail while allowing the 399.5-second response to settle normally.

## Decision

The treatment-neutral substrate is ready for mechanism iteration:

- independent scheduling remained live around slow requests;
- intermediate verification was bounded, asynchronous, and deduplicated in
  the preceding Stage 2 canary;
- final judge compatibility remained authoritative;
- all cost and timeout accounting was complete; and
- concurrent endpoint access succeeded without observed Qwen throttling.

Do not spend a larger evaluation-style wave on the current C1+ rule unchanged.
Its packets are too rare at a four-call ceiling, and the sole consumed hard-case
packet did not help. The next mechanism iteration should strengthen the
decomposition contract itself—what verified helpers/residual subgoals are
extracted and how the receiving track is asked to fill them—while retaining C0+
as the within-track salvage control and the now-validated common substrate.

## Artifacts

- `plan.json`: frozen matched design and resources.
- `dispatch/`: exact per-cell descriptors.
- `tasks/`: complete evaluator outputs, transcripts, events, solutions,
  checkpoints, and provenance.
- Remote root:
  `/opt/salvage-progress-packets-v1-stage3-putnam-a2-20260902T054000Z`.

All six remote cells are terminal. Historical tmux monitors on workers 1–4
were neither reused nor interrupted. No experiment container remains running.
