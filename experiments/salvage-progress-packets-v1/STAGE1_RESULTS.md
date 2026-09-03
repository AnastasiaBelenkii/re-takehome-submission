# Stage 1: deterministic and judge-facing canaries

## Frozen candidate

- Code commit: `d02a0e79aa794b4ff7b1bf4918f50b0085fc365e`
- Remote canary checkout: `takehome-worker-9:/opt/salvage-stage1-d02a0e7`
- Pinned Lean image: the unchanged collaboration-engine-v2 digest
- Provider/model calls: zero

## Deterministic suite

The focused collaboration, launcher, and Stage 3 tests passed 32/32 locally.
They cover, among other existing contracts:

- compiler-positioned span and suffix construction;
- statement/type and unpositioned diagnostic fail-closed behavior;
- rejection of zero-retention whole-proof placeholders;
- `sorry` exclusion from checkpoints and final solutions;
- C0+ within-track partial-state repair;
- C1+ compiler-grounded progress exposure;
- latest-wins queue replacement and provenance;
- unchanged online microcell and Stage 3 launcher contracts.

The repository-wide suite reported 110 passed and 9 skipped. Its sole failure
is the pre-existing frozen solo-baseline hash assertion: this repaired branch's
sample-problem manifest is intentionally not byte-identical to that historical
baseline fixture.

## Remote pinned-Lean preflight

The no-key preflight used the fresh detached checkout and a pre-existing
dependency-only virtual environment with the fresh checkout forced first on
`PYTHONPATH`. All 16 pristine challenges retained their required declarations;
none timed out. The deterministic call-zero tactic solved only `p05`, matching
the expected current-base behavior.

## Fresh Comparator boundary

On `p01_linear`:

- a partial file containing `sorry` was rejected by warm Lean;
- the same file filled with `linarith` was accepted by warm Lean;
- the filled file passed a fresh Comparator with exit code 0;
- fresh Comparator duration was 147.719 seconds on worker 9.

An initial 60-second diagnostic Comparator run timed out even on the valid
filled proof. This was below the actual 180-second profile and is not the
promotion result. It is nevertheless operational evidence that the cold judge
path has a large fixed latency. Online cells therefore retain a 240-second
verification reserve and the real 180-second Comparator timeout.

## Decision

Stage 1 passes for the bounded Stage 2 microcell. Partial state remains wholly
internal and the completed proof survives the actual fresh judge. Cold
Comparator latency and extra salvage-check duration remain explicit
guardrails.
