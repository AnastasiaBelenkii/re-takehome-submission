# re-takehome-submission

Verified Mechanisms Research Engineer take-home, Jacob Belenkii, September 2026. Two fixed models (Qwen 3.5 Flash, GPT-OSS 120B) prove Lean 4 theorems under a pinned Comparator, $1 and eight hours per problem.

**Writeup:** `writeup.pdf` (12 pages plus appendices). Section 1 has the answers.

**Submitted agent:** `submission/agent.py`, condition `c1plus-fill-reserve`: two asynchronous model tracks with a warm-Lean repair loop and partial-proof salvage, compiler-grounded progress packets between the tracks, one reserved call, and a fresh pinned Comparator on every warm-accepted candidate. `scripts/judge_check.sh` passes from a fresh clone of `main` (commit `9333436`).

**Results in one line:** the two-model portfolio solves the union of what each model solves alone, and that union is Qwen's set; letting the tracks exchange packets changes nothing detectable (talking minus silent −0.04, 95% interval −0.20 to +0.13, on the four band problems at six seeds).

**Repository map**

- `submission/` promoted agent and judge entrypoint
- `src/re_harness/` wrapper around the kit (Lean REPL client, Comparator runner, import canonicalization)
- `experiments/` one directory per wave with `PLAN.md`, `plan.json`, results, and per-stage notes (`online-development-v1/`, `salvage-progress-packets-v1/`, `salvage-fill-reserve-v2/`, `stage5-band/`, `stage5-solo/`)
- `experiments/analysis/` scripts and CSVs behind every table and figure in the writeup
- `fable-5-1-report-online-development-v1.md` the literature review that set the design
- `outputs/baseline/` supplied-agent runs

**Evidence branches** (per-cell `result.json`, `events.jsonl`, `transcript.json`, `solution.lean`, provenance): `evidence/results-20260902` (Wave C re-grade, Wave D band study, single-track solos), `evidence/online-development-v1-stage3-2e157547` (Wave A), `evidence/run-data-e8af4fb7d278` (Wave C transcripts).

**Reproducing a number:** every figure in the writeup names its archive root; `experiments/analysis/waveD_analysis.py --glob '<archive>/**/result.json'` regenerates the Wave D tables and curves.

**Tools disclosure:** harness and orchestration code were written with OpenAI Codex on the experiment workers under my direction and review; analysis, figures, and the writeup draft with Claude (Anthropic), with read access to the repository. Design, conditions, gates, and promotion decisions are mine; every number in the writeup was checked against the artifact it cites.
