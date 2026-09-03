# Stage 5 four-arm powered band study

Wave D compares the single-track `qwen-solo-plus` and `gptoss-solo-plus`
controls with the `c0plus-reserve` and `c1plus-fill-reserve` two-track
portfolios. The main ITT matrix contains four mechanically selected band
problems, six new fixed seeds, and four arms (96 cells). Each solo retains the
portfolio track budget of 25 calls; same-model two-track performance is an
analytical portfolio estimate from the single-track rates.

A problem entered the band exactly when the graders'-protocol outcomes across
all Wave A and C portfolio cells contained at least one Comparator pass and at
least one failure. Applied before launch, that rule selected p03, p07, p08, and
p09. The rmo_2000_6 regrade did not flip and therefore did not enter the band.

The fixed launch order begins with an extra p03 seed-1729 C0+/C1+ pair as an
operational observation, not a gate. The main matrix then cycles p03, p07, p08,
p09 within every seed. All four arms of a problem-seed block are adjacent, and
the dispatcher permits at most two incomplete blocks. The earlier p07
seed-1729 canaries remain separately archived as extra portfolio-arm cells.

Relative to Stage 3 matched v1, only Comparator timeout (420s), verification
reserve (480s), and outer time (2100s) change. Analysis is intention-to-treat
over all cells completed at the recorded analysis time; incomplete cells are
reported as incomplete and are never retried.
