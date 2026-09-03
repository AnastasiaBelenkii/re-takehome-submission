# Stage 6 calibration

Qwen solo-plus, seeds 7001–7008, at most 10 calls per cell.

| Problem | pass@8 | Known class |
|---|---:|---|
| p01_linear | 8/8 | ceiling |
| p02_frac_cancel | 8/8 | ceiling |
| p03_sq_ge_two_ab | 8/8 | band |
| p04_sum_sq | 8/8 | ceiling |
| p05_gcd_mersenne | 8/8 | ceiling |
| p06_pow_mod | 7/8 | ceiling |
| p07_least_divisible | 5/8 | band |
| p08_sum_products | 8/8 | band |
| p09_imo1964 | 1/8 | band |
| p10_factorial_pow | 7/8 | ceiling |
| putnam_2018_a1 | 0/8 | floor |
| putnam_2020_a2 | 0/8 | floor |
| rmo_2000_2 | 0/8 | floor |
| rmo_2000_3 | 0/8 | floor |
| rmo_2000_6 | 0/8 | unclassified (import-fix audit case) |
| rmo_2001_2 | 0/8 | floor |

The known ceiling, floor, and band labels above were fixed in the assignment extension before this calibration. The mechanically observed 1–7/8 band is: p06_pow_mod, p07_least_divisible, p09_imo1964, p10_factorial_pow.
