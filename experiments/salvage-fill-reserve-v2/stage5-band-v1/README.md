# Stage 5 powered band study

This preregistered Wave D compares `c0plus-reserve` with
`c1plus-fill-reserve` on `p03_sq_ge_two_ab`, `p07_least_divisible`,
`p08_sum_products`, and `p09_imo1964`. Mechanically, each selected problem has
at least one portfolio pass and one portfolio failure across Waves A and C;
the 600-second regrade left `rmo_2000_6` with no passes. Twelve new fixed seeds
produce 48 matched blocks and 96 ITT cells. The frozen experimental source is
`e8af4fb7d278cbf7c5e3e636716a6512f85da140`.

The only resource changes from Stage 3 matched v1 are Comparator timeout 420s,
verification reserve 480s, and outer time 2100s. Eight worker-local continuous
queues run one cell per worker, launch matched pairs together, and rotate the
condition-to-worker assignment. There are no fixed time slots.

The two `p07_least_divisible`, seed-1729 canaries are operational checks and
are excluded from the 96-cell ITT matrix. The main cells are released only
after at least one canary records a
completed passing verification and stops dispatching afterward. If both reach
the dispatch cutoff without that event, the wave halts.

Analysis is intention-to-treat over cells completed by 2026-09-03 03:30 PT.
Incomplete cells are reported as incomplete and are never retried.
