# Stage 6 expanded-band confirmation plan

Frozen before launch on 2026-09-03. The analysis population is intention-to-treat on every cell terminal at analysis time.

## Problems

The eight problems are selected from the completed expanded screen by distance to 4/8, with ties in the frozen Stage 6 plan order:

1. `aime_1983_p1`
2. `aime_1990_p4`
3. `algebra_amgm_sumasqdivbgeqsuma`
4. `aime_1990_p15`
5. `aime_1997_p9`
6. `algebra_others_exirrpowirrrat`
7. `algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7`
8. `algebra_9onxpypzleqsum2onxpy`

## Primary confirmation

- Seeds: 8101, 8102, 8103, 8104.
- Arms, adjacent within every block: `qwen-solo-plus`, `gptoss-solo-plus`, `c0plus-reserve`, `c1plus-fill-reserve`.
- Global order: seed-major, then the problem order above, then the arm order above. This freezes 128 cells before launch.
- Execution: one global FIFO with work-stealing across workers 1–8 and 10; executing worker is written into provenance and is not part of the design.
- Full 25 calls per model track; early stop on a Comparator pass; Comparator timeout 420 seconds; otherwise Wave D settings at commit `d43af0199db14b36e1761efc641aa00c2dbc3ffe`.
- Archive: `evidence/archives/stage6-confirm-20260903/`.

## Solo extension for the virtual-portfolio control

Only after all 128 primary cells have dispatched, and only if that occurs no later than 23:00 PT, append 64 separately labelled cells: the same problem order, seeds 8105–8108, and adjacent arms `qwen-solo-plus`, `gptoss-solo-plus`. Calls and verification settings are identical to the primary confirmation. The global order is seed-major, then problem, then arm. These cells share the confirmation archive and use `analysis_set = solo_extension_virtual_portfolio`.
