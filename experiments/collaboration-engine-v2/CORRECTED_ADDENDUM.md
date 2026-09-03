# Corrected challenge addendum

This post-hoc addendum reruns the three challenges changed by upstream commits
`6a33f70` and `7b245af` without altering or pooling them silently into the frozen
v2 run. The agent, C0/C1/C2 manifests, shallow resource profile, model pair,
temperature, generation limit, seeds, and retry policy remain those of production
agent commit `73eb36dbe07abfa23141ffbabce4c4d65d7567a8`.

The corrected challenges are:

- `rmo_2000_6`: false second minimum corrected from 20 to 10.
- `putnam_2020_a2`: the answer `4 ^ k` is inlined to prevent circular definitions.
- `putnam_2018_a1`: the six answer pairs are inlined to prevent circular sets.

Each problem receives three paired replications under C0, C1, and C2, for 27
shallow cells. Seeds are 1729, 2718, and 3141. A deterministic rotating condition
order prevents any one condition from always leading a block. The addendum drains
through one DigitalOcean worker while the original frozen deep waves occupy three
workers, preserving the four-active-problem envelope.

The original artifacts remain immutable. Corrected cells are analyzed as a
separately labeled addendum. Any combined corrected-dataset analysis excludes all
old cells for these three challenges and uses these cells instead; it continues to
show original-manifest intention-to-treat results separately.

