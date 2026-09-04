# C0-QQ gate

Status: **PENDING SMOKE**  
Base: `d43af0199db14b36e1761efc641aa00c2dbc3ffe`  
Implementation commit: `04cd01e076dbef613fa321647c405430f787b506`  
Pre-run record frozen: 2026-09-04 03:43:49 UTC

## Prediction (written before the run)

H1: `c0-qq` pass rate on the 32 blocks lies within ±0.05 of
`1 − (1 − p_Q)²` computed from the `qwen-solo-plus` cells on the same blocks.
Below by more than that: Qwen's draws are correlated within a problem. Above:
something beyond sampling is happening in a portfolio.

## Implementation gate

- `c0-qq` is the silent `none` strategy with salvage enabled, no reserved call,
  and two `qwen/qwen3.5-flash-02-23` tracks.
- Engine scheduling and result accounting are keyed by explicit track IDs
  `qwen#1` and `qwen#2`; provider requests retain the unchanged model ID.
- The two tracks split the cell seed into distinct deterministic provider
  sub-seeds, recorded under their track metadata.
- Existing arms retain model IDs as their track IDs and retain the original
  cell seed, preserving their request and metadata paths.

## Tests

- Full non-Docker suite: **PASSED**, 135 passed, 9 skipped, 1 expected failure.
- Focused collaboration/candidate suite: **PASSED**, 47 passed.
- Same-model unit smoke: **PASSED**; two Qwen calls, distinct sub-seeds, both
  track records present, and the first completed Comparator check passed.

## Recorded-observation byte identity

**PASSED.** The regression fixture reconstructs the first-round calls from the
recorded Stage 5 `p07_least_divisible`, seed 6211 observation. The generated
request bytes are identical between `c0plus-reserve` and
`c1plus-fill-reserve` and retain the recorded SHA-256 values:

- Qwen: `08ea22bc70705e8307f83a91ecfbc5acf5543c47d7a95d93bd69deb36499d626`
- GPT-OSS: `43ec15c37174ee097881cbebd77004898f3039122cfb3f4c0841b3426b5d0139`

The source observations are the paired Stage 5 archive cells for
`p07_least_divisible`, seed 6211, conditions `c0plus-reserve` and
`c1plus-fill-reserve`.

## Online smoke

Not launched at the time this pre-run gate was frozen. The immutable plan is
`qq-smoke-plan.json`: two `p07_least_divisible` cells, seeds 9201–9202, worker
9, at most eight calls per track and $0.25 per cell. This section must say
**PASSED** before Part B is eligible.
