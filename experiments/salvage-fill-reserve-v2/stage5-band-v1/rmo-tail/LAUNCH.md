# Launch record

- Gate run: `import-fix-gate-once-rmo_2000_6-c1plus-fill-reserve`
- Gate outcome: Comparator proof failure (`unsolved goals`), answer shape
  passed, no statement-mismatch error, and no timeout.
- Runtime SHA: `853884ebecf0f33e0af5b96c23d797a36bfa7121`
- Queue policy: the 02:30 PT main-wave cutoff was removed by user direction.
  Start only after every main Wave D cell has been dispatched; use workers
  1--8 only as each becomes free; never kill a running cell; no retry of a
  paid task.
