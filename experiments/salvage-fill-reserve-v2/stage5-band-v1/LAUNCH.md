# Launch record

- Experiment: `salvage-fill-reserve-v2-stage5-band-v1`
- Runtime source: `d43af0199db14b36e1761efc641aa00c2dbc3ffe`
- Workers: `takehome-worker-1` through `takehome-worker-8`
- Main ITT cells: 96
- New operational p03/1729 cells: 2, excluded from main ITT matrix
- Prior p07/1729 canaries: 2, separately archived extra portfolio-arm cells
- Scheduling: continuous availability-aware dispatch, at most eight cells and two incomplete four-arm blocks
- Evidence destination: `evidence/archives/stage5-band-20260903/`
- Status: frozen; dispatch pending

The failed p07 canary gate is retired by the final 01:10 PT plan. It was
uninformative because neither agent found a warm-accepted candidate, so no
verification could start. Wave D is released without a gate. Existing paid
cells are never interrupted, and fixed block order is never adapted to results.
