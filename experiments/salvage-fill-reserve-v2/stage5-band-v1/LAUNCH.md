# Launch record

- Experiment: `salvage-fill-reserve-v2-stage5-band-v1`
- Frozen source: `e8af4fb7d278cbf7c5e3e636716a6512f85da140`
- Workers: `takehome-worker-1` through `takehome-worker-8`
- Main ITT cells: 96 (all gated and not launched)
- Operational canaries: 2 (excluded from the ITT matrix)
- Scheduling: continuous worker-local queues, eight concurrent cells maximum
- Evidence destination: `evidence/archives/stage5-band-20260903/`
- Fresh remote checkout: `/opt/salvage-fill-reserve-v2-stage5-e8af4fb-20260903T0618Z/checkout`
- Remote result root: `/opt/salvage-fill-reserve-v2-stage5-band-v1-20260903T0618Z`
- Canary launch: 2026-09-02 23:16:25 PT (workers 1 and 2 only)

## Canary decision

At 2026-09-02 23:33 PT both canaries had reached the 960-second dispatch
cutoff. C0+ dispatched 31 calls and C1+ dispatched 22; both recorded zero
warm-Lean successes and an empty `verification_events` list. The preregistered
release gate therefore failed. Wave D is halted and no main ITT cell was
released.
