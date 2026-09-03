# Stage 2: first matched C0+/C1+ microcell

## Frozen design

- Code SHA: `d02a0e79aa794b4ff7b1bf4918f50b0085fc365e`
- Problem/seed: `p06_pow_mod`, 1729
- C0+: worker 8, within-track salvage, no peer access
- C1+: worker 9, identical salvage plus event-driven latest-wins progress packets
- Ceiling: four calls per model, $0.25 per cell
- Salvage check timeout: two seconds
- Final Comparator timeout: 180 seconds

The first-round requests were byte-identical by construction, but provider
responses diverged before any communication occurred. This pair therefore
cannot attribute its score discordance to treatment.

## Outcomes

| Arm | Passed | Calls | Wall seconds | Spend |
| --- | ---: | ---: | ---: | ---: |
| C0+ | yes | 5 | 599.544 | $0.004811845 |
| C1+ | no | 8 | 822.842 | $0.005326427 |

C0+ produced no useful salvage skeleton. Qwen generated two warm-valid complete
candidates. The first intermediate fresh Comparator timed out after 182.770
seconds; the second passed after 170.961 seconds. Final independent judging
also passed. The selected proof was ordinary Qwen self-repair, not salvage.

C1+ produced no warm-valid complete candidate. Final Comparator rejected its
best admissible no-`sorry` checkpoint with the residual goal
`7 ^ 2026 % 100 = 49`; this was a real proof failure, not a gate error.

## Mechanism trace

C1+ generated four compiler-grounded progress packets and consumed one:

1. Qwen call 1 yielded a warm-compiling five-line suffix skeleton.
2. Qwen call 4 improved this to a warm-compiling 22-line skeleton.
3. Latest-wins replacement discarded the stale first packet.
4. GPT call 2 consumed Qwen's 22-line skeleton and residual diagnostic.
5. That packet-exposed GPT response was not complete, but its failing suffix
   could itself be salvaged into a compiling six-line GPT skeleton.
6. GPT call 4 later produced another compiling five-line skeleton.
7. Four bidirectional packets were generated; one was consumed, two were
   replaced before use, and one remained pending after Qwen exhausted calls.

This is strong evidence that the proposed decomposition mechanism occurs and
that packet-exposed work can yield new compiler-validated partial state. It is
not evidence that borrowed material caused a final solve.

## Latency and substrate findings

- Intermediate candidate verification is a synchronous fresh Comparator.
  Every warm-valid complete candidate freezes agent scheduling for up to 180
  seconds, even while another model response has already completed.
- The final winner is checked fresh again, so a successful trajectory can pay
  both intermediate and final cold-judge costs.
- C1+'s packet-bearing GPT call took 353.126 seconds. Its next GPT repair call
  took 222.235 seconds. The HTTP client's 180-second value is a per-read timeout,
  not a hard whole-request deadline.
- Salvage verification itself was cheap in this cell: successful suffix checks
  were subsecond. Cold Comparator and provider tails dominated wall time.

## Comparison to repaired C0/C1/C2 on p06

All nine prior repaired Stage 3 `p06` cells passed under the larger 25-call
ceiling. Old C0 used 6-18 calls, C1 11-14, and C2 3-11. Thus `p06` is useful for
mechanism/latency diagnosis but is not a discriminating score problem.

Old C1/C2 packets were consumed but contained generic failed candidates and
diagnostics, with no solve attributable to peer information. C1+ shows a more
legible causal funnel: compiler-validated progress was produced, delivered,
used, and followed by new compiler-validated partial state. Its current
latency and completion behavior are worse, so mechanism quality has not yet
translated into solver quality.

## Decision

Do not expand this condition yet. Preserve the salvage/progress mechanism, but
repair two treatment-neutral substrate defects and rerun both arms:

1. make intermediate candidate verification asynchronous, hash-deduplicated,
   and single-flight while retaining final fresh Comparator authority;
2. add an explicit hard model-request wall deadline with honest uncertain-cost
   accounting on cancellation.

After the repaired matched canary, move to a harder problem such as
`putnam_2020_a2`, where offline salvage yield was high and baseline outcomes are
less saturated.
