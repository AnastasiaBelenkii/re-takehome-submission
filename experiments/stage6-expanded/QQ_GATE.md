# C0-QQ gate

Status: **PASSED**

Base: `d43af0199db14b36e1761efc641aa00c2dbc3ffe`

Implementation commit: `04cd01e076dbef613fa321647c405430f787b506`

Smoke source branch SHA: `8680cc70d87524e8ff4a92ee610a982a71dfaf89`

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

**PASSED.** The immutable `qq-smoke-plan.json` ran sequentially on worker 9
against the source SHA above: two `p07_least_divisible` cells, seeds 9201–9202,
at most eight calls per track and $0.25 per cell.

| Seed | Result | `qwen#1` | `qwen#2` | Provider sub-seeds |
|---:|:---:|---:|---:|:---|
| 9201 | pass | 8 calls | 8 calls | 1969822975, 1959749056 |
| 9202 | fail | 8 calls | 8 calls | 1304153483, 860350474 |

Both cells record two separate track entries, both entries name
`qwen/qwen3.5-flash-02-23`, all 32 logical calls were physically dispatched,
and no packet or reserved-call path was active. On seed 9201, the first
Comparator invocation completed with `passed=true` on Qwen call 7; the queued
second candidate was then superseded by verified success. The observed smoke
rate was 1/2 and total provider cost was $0.070838625.

The complete descriptors, provenance, transcripts, events, checkpoints, and
terminal results are archived under `qq-smoke/` beside this gate.

This gate authorizes Part B under the user's separate launch conditions; Part
B was not launched in this development session.
