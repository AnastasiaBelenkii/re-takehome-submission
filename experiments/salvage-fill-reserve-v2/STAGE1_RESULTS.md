# Stage 1: offline and pinned-image results

The new condition is implemented without changing the frozen C0+/C1+ strategy
identifiers. `c1plus-fill-reserve` uses `progress-fill-event-latest-v2`;
`c0plus-reserve` uses no packet strategy. Both enable the same within-track
salvage and accept the same reserve settings from the run descriptor.

Deterministic scheduler tests establish that:

- Qwen spends its unreserved calls without waiting for GPT;
- its final call remains undispatched while GPT can still produce progress;
- a GPT packet unlocks that call and is consumed in the fill prompt;
- the fill prompt contains no generic "critically evaluate" instruction;
- the packet event records production, consumption, and delivery delay; and
- the matched no-packet control releases its identical reserve only after GPT
  exhausts its calls.

Local test results at the pre-canary branch state were 115 passed and nine
skipped. The only failure was the known historical solo-baseline manifest hash
assertion: the current problem manifest contains the already-adopted upstream
problem fixes and is intentionally not byte-identical to the older frozen
baseline manifest.

All nine Docker integration tests then passed against the pinned image
`ghcr.io/verifiedmechanisms/re-takehome-lean@sha256:ee48287cd31c0a7df572093a879ed7289c2f01fec6c7af8716c605fc8c670c39`
in 311.25 seconds. These tests exercise warm Lean, timeout cleanup,
checkpointing, and the real final fresh-Comparator path.

Stage 1 passes. No worker or paid endpoint was used during this stage.
