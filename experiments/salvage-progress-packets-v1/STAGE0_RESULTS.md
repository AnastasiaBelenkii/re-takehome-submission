# Stage 0: salvage replay results

## Preregistered mechanism question

Changing failed-candidate repair from ordinary diagnostic feedback to
compiler-validated partial-proof salvage should create reusable proof progress
on recent hard failures because Lean can identify a failing source region while
accepting the surrounding structure. It is falsified if useful skeletons are
rare, unsafe, or too slow to validate. C0+ and C1+ receive byte-identical
within-track salvage; the only independent variable in their later comparison
is whether validated progress is exposed to the peer.

These development measurements are descriptive and underpowered for score
effects. Stage 0 tests mechanism availability and safety, not solve-rate uplift.

## Evidence source

- Local immutable collection of the repaired Stage 3 wave:
  `/opt/takehome-results/online-development-v1-stage3-v1-20260901T215645Z-2e157547`
- 81 transcripts, 1,321 recorded calls, and 1,196 exact transcript-to-Lean-check
  joins by checked-source SHA-256.
- 759 failed checks were structurally eligible; 705 were unique failure states.
- The replay made zero model/provider calls.

## Refinement forced by the evidence

The first permissive replay compiled 678/705 proposed files, but 557 were
whole-proof placeholders retaining zero proof-body lines. That 96.2% figure is
not useful salvage yield and must not be cited as such. Live C0+/C1+ now reject
all zero-retention proposals and fall back to ordinary repair.

The final rule tries a compiler-positioned failing span, then a failing suffix,
and accepts a skeleton only when:

1. it retains at least one proof-body line;
2. warm Lean reports no errors or timeout; and
3. the only incompleteness is explicit `sorry` partial state.

Partial state cannot be returned, checkpointed, fresh-verified, or treated as
success.

## Strict replay

The checked-in `stage0b-salvage-replay.json` is a deterministic hash-selected
sample of 100 unique eligible failures, using a two-second timeout per extra
salvage check.

| Measure | Result |
| --- | ---: |
| Useful compiling skeletons | 24 / 100 |
| GPT-OSS useful skeletons | 18 / 45 |
| Qwen useful skeletons | 6 / 55 |
| Extra warm checks | 180 |
| Extra check duration | 152.702 s |
| Extra check timeouts | 15 |
| Diagnostic-span successes | 1 |
| Failing-suffix successes | 23 |

A ten-second ceiling produced 25/100 on the identical sample. The two-second
ceiling therefore lost one skeleton while materially bounding the tail and is
the initial online setting.

## Decision

Stage 0 passes for a small C0+/C1+ online mechanism test. A 24% useful yield is
large enough to expose the proposed behavior, and retained prefixes range from
one to 21 lines in this sample. It does not justify a broad or deep wave.

Promotion guardrails:

- measure extra salvage-check time and completed model calls per cell;
- require observed within-track skeleton reuse in C0+;
- require actual peer packet production and consumption in C1+;
- do not interpret a small score difference as an uplift;
- stop if verification overhead materially reduces completed calls or if
  skeletons are routinely discarded rather than repaired.
