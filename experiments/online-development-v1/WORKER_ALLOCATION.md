# Worker allocation

> **Workers 8--9 are human-directed only. Worker 10 is the machine-controlled
> Humanize coordinator. Do not schedule automated experiment cells on workers
> 8--10.**

As of 2026-09-01, worker 10 is reserved for the outer optimization/control
loop. Its pre-install data snapshot is stored on worker 6 at:

```text
/opt/backups/takehome-worker-10-pre-autoopt-20260901T014800Z
```

Workers 1--7 are the prospective automated experiment pool. Workers 8--9 are
reserved for human-directed canaries, debugging, judge checks, and the
canonical experiment archive. Every launcher must still perform a live
reachability and idle-state preflight before assigning work.
Compatibility aliases map `takehome-worker-1` to the machine canonically named
`takehome-control` and `takehome-worker-5` to the replacement machine
canonically named `takehome-worker-5b`. The canonical aliases remain valid;
experiment plans should use the numbered worker aliases consistently.

The canonical consolidated archive is on worker 9; see
[EXPERIMENT_ARCHIVE_INDEX.md](EXPERIMENT_ARCHIVE_INDEX.md). Historical plans
that name workers 8--9 remain provenance records and may still be collected,
but must not be relaunched there by an automated controller.

This allocation is operational metadata, not an experimental condition.
Changing it requires updating this document and the dispatcher's reserved-host
guard in the same commit.
