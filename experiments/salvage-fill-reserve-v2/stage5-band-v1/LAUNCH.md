# Launch record

- Experiment: `salvage-fill-reserve-v2-stage5-band-v1`
- Runtime source: `d43af0199db14b36e1761efc641aa00c2dbc3ffe`
- Workers: `takehome-worker-1` through `takehome-worker-8`
- Main ITT cells: 96
- New operational p03/1729 cells: 2, excluded from main ITT matrix
- Prior p07/1729 canaries: 2, separately archived extra portfolio-arm cells
- Scheduling: continuous availability-aware dispatch, at most eight cells and two incomplete four-arm blocks
- Evidence destination: `evidence/archives/stage5-band-20260903/`
- Remote result root: `/opt/salvage-fill-reserve-v2-stage5-band4-v1-20260903`
- First dispatch: 2026-09-03 00:28 PT
- Status: released without a gate; continuous dispatch active

At 02:15 PT the user removed the planned 02:30 PT dispatch cutoff. The main
queue continues in its frozen order through the final deadline. The separate
rmo tail waits until every main-matrix cell has been dispatched, so it cannot
compete with the main queue.

Evidence snapshots are scheduled for 03:15 PT and 04:00 PT. The rmo tail is
strictly non-interleaved and launches only after the final main cell dispatches
and the capped counterfactual packet replay completes. The tail remains queued
through the replay; running cells are never killed.

The failed p07 canary gate is retired by the final 01:10 PT plan. It was
uninformative because neither agent found a warm-accepted candidate, so no
verification could start. Wave D is released without a gate. Existing paid
cells are never interrupted, and fixed block order is never adapted to results.

At 00:30 PT, dispatch paused after the observation pair exceeded the planned
"warm accepted plus five later calls" alert. Live `worker-config.json` and the
worker process environment both contained Comparator timeout 420s,
verification reserve 480s, and outer time 2100s. Both cells had active fresh
Comparator containers. Dispatch resumed at 00:31 PT without changing the
environment: the alert detects a slow asynchronous Comparator, not missing
environment propagation. The first C0+ in-agent verification passed in
205.6s, and both p03 observation cells ultimately passed.
