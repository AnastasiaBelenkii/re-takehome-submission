# Launch record

- Frozen source: `3fc35ad4de4cb44724296084a1898bfd4efe2fa7`
- Planned workers: `takehome-worker-1` through `takehome-worker-8`
- Cells: 32
- Launch gate: after the final Wave D dispatch
- Fresh checkout: `/opt/salvage-fill-reserve-v2-stage5-solo-3fc35ad-20260903T0637Z/checkout`
- Result root: `/opt/salvage-fill-reserve-v2-stage5-solo-v1-20260903`
- Launched: 2026-09-02 23:39:10 PT
- Worker-local tmux session: `sfrv2_stage5_solo_3fc35ad`

At launch all eight queues contained four cells: one running and three
pending. Each queue is durable on its worker and never retries a cell.
