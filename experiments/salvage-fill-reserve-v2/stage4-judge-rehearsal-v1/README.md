# Stage 4 judge rehearsal

Status: prepared, not authorized for paid launch.

This is an eleven-cell promotion study under the published eight-hour and $1
per-problem envelope. The first block runs all five available designs on
`p07_least_divisible`, the best-replicated non-saturated problem in the recent
Stage 3 data. The second block uses a new replication of `p09_imo1964` for the
strategic shortlist: legacy C2, C0+reserve, and C1+fill-reserve. P09 is hard but
has moved off zero in corrected shallow data; unlike Putnam 2020 A2, it can
therefore provide both stress and score signal.

The third block runs the same three-arm shortlist on `putnam_2020_a2`. It is a
deliberate floor-level stress test: the recent data are 0/10, so its principal
outcomes are whether deeper search moves off zero and whether the mechanisms
remain productive, accounted, and verifiable under a genuinely hard task. It
is not the primary score-sensitive comparison.

The five p07 cells answer the whole-design promotion question. The matched
C0+reserve/C1+fill-reserve contrasts on both problems remain the clean evidence
for collaboration because peer access is their only condition difference.
C2 is a promotion candidate and historical bridge, but comparisons between C2
and either plus arm also include salvage and scheduling changes.

Factories in `submission/candidates.py` make every arm self-contained under
judge defaults: eight hours, an unlimited call count bounded by the $1 ledger,
and a dispatch cutoff twelve minutes before the evaluator deadline. They do
not change the current `submission.agent` default. Once a condition is chosen,
promotion is an explicit import change followed by the unmodified published
command and `scripts/judge_check.sh` from a fresh checkout.

The six historical C0/C1/C2 deep cells are not pooled with this rehearsal.
They ran at pre-audit SHA `73eb36d` with the critical gate and scheduling
defects, all failed, and dispatched between 44 and 454 calls per cell.
