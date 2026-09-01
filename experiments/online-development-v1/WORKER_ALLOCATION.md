# Worker allocation

> **Worker 10 is not an experiment worker. Do not schedule harness cells on
> `takehome-worker-10`.**

As of 2026-09-01, worker 10 is reserved for the outer optimization/control
loop. Its pre-install data snapshot is stored on worker 6 at:

```text
/opt/backups/takehome-worker-10-pre-autoopt-20260901T014800Z
```

The experiment-worker namespace is workers 1--9. Every launcher must still
perform a live reachability and idle-state preflight before assigning work.
From the current development host, workers 2, 3, 4, 6, 7, 8, and 9 are
reachable and idle; the `takehome-worker-1` and `takehome-worker-5` aliases do
not currently resolve. Historical plans may refer to a separate
`takehome-worker-5b` alias, which is not evidence that worker 5 is currently
available.

This allocation is operational metadata, not an experimental condition.
Changing it requires updating this document and the dispatcher's reserved-host
guard in the same commit.
