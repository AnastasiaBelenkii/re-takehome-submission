# Stage 6 expanded-set plan

Frozen before any expanded-problem paid call. The calibration in
`CALIBRATION_PLAN.md` runs and is summarized first; the expanded inputs may be
prepared meanwhile, but their screen remains gated on the calibration's final
push.

## Source and mechanical selection

Source: the miniF2F Lean 4 test split, repository
`https://github.com/yangky11/miniF2F-lean4`, commit
`5746b7d6c47855ce1294bed87329618ff7f1bc31`. The source is MIT licensed,
Copyright Meta Platforms, Inc. and affiliates. Native order is the import order
in `MiniF2F/Test.lean`.

Starting at the first import, a statement survives iff it (a) is not one of the
16 supplied statements, (b) begins with the exact header `import Mathlib`, (c)
builds with its `sorry` against pinned image
`ghcr.io/verifiedmechanisms/re-takehome-lean@sha256:ee48287cd31c0a7df572093a879ed7289c2f01fec6c7af8716c605fc8c670c39`,
and (d) is not closed when every tactic hole is replaced by the frozen cascade
`first | omega | norm_num | nlinarith | linarith | ring | aesop | simp_all`.
Selection stops at 32 survivors. All first 32 source statements survived, so
the exclusion ledger is empty; no later source statement was considered or
hand-picked.

The frozen survivors, in source order, are:

1. `aime_1983_p1`
2. `aime_1983_p2`
3. `aime_1983_p3`
4. `aime_1984_p1`
5. `aime_1984_p7`
6. `aime_1987_p5`
7. `aime_1988_p8`
8. `aime_1989_p8`
9. `aime_1990_p15`
10. `aime_1990_p4`
11. `aime_1991_p9`
12. `aime_1994_p3`
13. `aime_1995_p7`
14. `aime_1997_p9`
15. `aime_1999_p11`
16. `algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7`
17. `algebra_9onxpypzleqsum2onxpy`
18. `algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2`
19. `algebra_absapbon1pabsapbleqsumabsaon1pabsa`
20. `algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1`
21. `algebra_amgm_sum1toneqn_prod1tonleq1`
22. `algebra_amgm_sumasqdivbgeqsuma`
23. `algebra_apbmpcneq0_aeq0anbeq0anceq0`
24. `algebra_apbon2pownleqapownpbpowon2`
25. `algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3`
26. `algebra_bleqa_apbon2msqrtableqambsqon8b`
27. `algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778`
28. `algebra_ineq_nto1onlt2m1on`
29. `algebra_others_exirrpowirrrat`
30. `algebra_sqineq_at2malt1`
31. `algebra_sqineq_unitcircatbpabsamblt1`
32. `algebra_sqineq_unitcircatbpamblt1`

Each is materialized under `experiments/stage6-expanded/problems/` with the
unchanged source as `challenge.lean`, a source-identifying `problem.md`, and a
generated manifest entry.

## Band-finding screen

Commit: `d43af0199db14b36e1761efc641aa00c2dbc3ffe`. First arm:
`qwen-solo-plus`, seeds 7001–7008, at most 10 model calls per cell, early stop
only on a Comparator pass: 256 cells. Global order is seed-major then the 32
problems above; global indices are round-robin over workers 1–8 so any cutoff
covers the problem list evenly. If Qwen completes with time before the launch
deadline, append `gptoss-solo-plus` at seeds 7001–7004 in the same order: 128
cells. “Wall time allows” is fixed before outcomes are seen: GPT-OSS launches
iff all 256 Qwen cells finish by 12:15 PT. No pending cell may dispatch at or
after 14:00 PT.

Other settings match Wave D: temperature 0.2, 12,000 generation tokens, $1 per
cell, 120-second warm Lean, 420-second Comparator, 960-second dispatch cutoff,
2,100-second outer limit, and two restarts. Archive root:
`evidence/archives/stage6-pass8-20260903/`.

Band membership is fixed mechanically after the screen: Qwen 1–7 passes of 8,
or GPT-OSS 1–3 passes of 4. `BAND.md` reports every observed denominator and
the resulting list.

## C. Primary confirmation

This launches only if B finishes before 13:30 PT. Keep at most six band
problems, selecting the six whose Qwen count is nearest 4/8 (ties retain source
order). For each selected problem and seed 8101–8104, dispatch adjacent fixed
blocks in arm order `qwen-solo-plus`, `gptoss-solo-plus`, `c0plus-reserve`,
`c1plus-fill-reserve`. Every track receives the full 25-call ceiling; other
settings match Wave D. Archive root:
`evidence/archives/stage6-confirm-20260903/`. A fifth
`c2plus-sketch-fill` arm is appended only if it exists on a branch and
`SKETCH_GATE.md` already says PASSED, and is recorded under its own commit.

## C.2. Solo extension

After every primary C cell has dispatched, and only while the time is still
before 14:00 PT, append a separate fixed plan entry for the two solo arms only:
`qwen-solo-plus` then `gptoss-solo-plus`, seeds 8105–8108, on the same selected
band problems, with the full 25-call ceiling and Wave D settings. These cells
share the confirmation archive but retain a distinct `analysis_set` and plan
entry. No C.2 cell may dispatch before all primary C cells have dispatched, and
none may newly dispatch at or after 14:00 PT.
