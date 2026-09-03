# Stage 6 calibration plan

Frozen before dispatch. This calibration applies the Stage 6 screen to all 16
supplied problems: one `qwen-solo-plus` cell for each problem at each of seeds
7001–7008 (128 cells). Each cell uses commit
`d43af0199db14b36e1761efc641aa00c2dbc3ffe`, at most 10 Qwen calls,
temperature 0.2, 12,000 generation tokens, a $1 ledger, a 120-second warm-Lean
timeout, a 420-second Comparator timeout, a 960-second dispatch cutoff, and a
2,100-second outer limit.

The immutable global order is seed-major, then the repository sample-problem
order: p01_linear, p02_frac_cancel, p03_sq_ge_two_ab, p04_sum_sq,
p05_gcd_mersenne, p06_pow_mod, p07_least_divisible, p08_sum_products,
p09_imo1964, p10_factorial_pow, putnam_2018_a1, putnam_2020_a2, rmo_2000_2,
rmo_2000_3, rmo_2000_6, rmo_2001_2. Global dispatch indices are assigned
round-robin to workers 1–8, leaving each worker a frozen 16-cell local queue.
No queue is reordered from outcomes. The archive root is
`evidence/archives/stage6-calibration-20260903/`.

Calibration dispatch remains gated on the final A2 replay push. Already-running
paid cells are never stopped or retried; the worker-local queue controller moves
to the next descriptor only after the current cell writes its terminal marker.
