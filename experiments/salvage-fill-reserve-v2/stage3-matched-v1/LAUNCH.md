# Launch record

- Source SHA: `e8af4fb7d278cbf7c5e3e636716a6512f85da140`
- Remote checkout: `/opt/salvage-fill-reserve-v2-stage3-e8af4fb/checkout`
- Remote result root:
  `/opt/salvage-fill-reserve-v2-stage3-matched-v1-20260902T071500Z`
- Workers: `takehome-worker-1` through `takehome-worker-8`
- Worker-local tmux session: `sfrv2_stage3_e8af4fb`
- First scheduled slot: 2026-09-02 07:08 UTC
- Last scheduled slot: 2026-09-02 10:20 UTC
- Cells: 56, seven per worker
- Maximum authorized budget: $56; actual spend is read from complete ledgers

Immediately before launch, all fresh task namespaces and tmux session names
were absent. No worker had a running evaluator, microcell launcher, queue
controller, or Docker container. Detached historical administration and
monitoring sessions on workers 1–5 were identified and left untouched.

Each worker holds its own complete queue state and artifacts. Loss of the
initiating host does not stop dispatch. A missing local copy is never grounds
for retrying a remote cell; reconcile the remote queue state first.
