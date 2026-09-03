# Stage 3 matched C0+/C1+ wave

This wave reuses all 28 problem-seed blocks from
`online-development-v1-stage3-replication-v1`. With two conditions, it has 56
cells rather than the historical three-condition total of 84.

The primary comparison is paired `c1plus-fill-reserve` minus
`c0plus-reserve`. Both arms use identical within-track salvage, scheduling,
call ceilings, budgets, and idle reserve. Only the C1+ arm may receive the
other track's latest compiling skeleton, residual goals, and verified helper
declarations.

Eight worker-local queues run on workers 1–8. Each matched pair is concurrent;
condition assignment rotates between the two workers in its pair. The queues
continue if the initiating host is preempted. Worker 10 is prohibited, and
worker 9 remains an unused recovery/collection spare. Read-only preflight
found only detached historical monitoring shells on workers 1–5, no active
experiment processes or containers; those sessions are left untouched.

Successive blocks use fixed 32-minute UTC start slots. This keeps the matched
conditions temporally aligned without a host-side controller while leaving a
four-minute margin beyond the 28-minute cell ceiling. The runtime descriptor
records the actual launch time; the immutable queued descriptor records its
scheduled `not_before` time.

The frozen resource envelope matches historical Stage 3 where applicable:
$1 and 28 minutes per cell, a 16-minute dispatch window, 25 calls per model,
and the same generation and verification limits. New mechanism-specific
settings are one reserved fast-track call, a two-second salvage probe, and a
seven-minute model-call wall timeout.

Results are retained remotely until explicitly collected. A missing local
controller is not evidence that a cell failed and must never trigger a retry.
