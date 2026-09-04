# When Does Collaboration Help in Lean Proof Search?

Research Engineer take-home by Jacob Belenkii for Verified Mechanisms.

This repository studies a practical allocation question: given a fixed budget for proving a Lean theorem, should the system spend its next model calls on another independent search, a different model, or communication between searchers?

The two available models are `qwen/qwen3.5-flash-02-23` and `openai/gpt-oss-120b`. Every candidate is checked in Lean and final success requires acceptance by a fresh run of the pinned Comparator.

## Bottom line

In these experiments, collaboration helped primarily because it added another search trajectory. I did not find evidence that exchanging partial-proof messages improved the mixed-model portfolio.

| Evaluation | Qwen | GPT-OSS | Qwen + GPT-OSS, silent | Qwen + GPT-OSS, talking | Qwen + Qwen, silent |
|---|---:|---:|---:|---:|---:|
| Supplied mixed-outcome problems | 16/24 | 9/24 | 19/24 | 17/24 | - |
| Qwen-hard/variable replication set | 18/32 | 14/32 | 21/32 | 22/32 | **29/32** |

The first row repeats four supplied problems six times. The second uses four repetitions on eight miniF2F problems selected because short Qwen runs had variable outcomes. These are deliberately conditional evaluation sets, not estimates of performance over all Lean problems.

The useful distinction was:

- **Coverage:** a second independent search can solve problems missed by the first.
- **Model diversity:** it helps only when the other model rescues enough failures to justify the calls it receives.
- **Communication:** a message helps only if it changes the receiver's search trajectory. Verified-prefix messages did not produce a measurable benefit here.

On the replication set, the silent Qwen + Qwen policy was the strongest tested allocation. That result is specific to this harness and selected problem set, but it is enough to reject the assumption that a heterogeneous pair is automatically the best use of two search tracks.

## Submitted system

[`submission/agent.py`](submission/agent.py) runs one Qwen track and one GPT-OSS track concurrently. Each performs its own compiler-guided repair loop; candidates, compiler feedback, and model responses are not shared between tracks. The implementation preserves the judging contract and records the result, transcript, event log, and submitted Lean file for each problem.

The submitted agent is intentionally identified as a **silent portfolio**. The talking policies, same-model portfolio, replay studies, and development variants are experimental comparisons rather than hidden parts of the final entrypoint.

## Run the submission

Requirements: Docker, Python 3.11+, approximately 20 GB of disk space, and an OpenRouter API key for model calls. Lean and Mathlib run inside the pinned container image.

```bash
bash scripts/setup.sh
cp .env.example .env
# Add OPENROUTER_API_KEY to .env

bash scripts/smoke_test.sh   # container + Comparator; no API key required
bash scripts/judge_check.sh  # one-problem end-to-end judging contract
```

See [`docs/SETUP.md`](docs/SETUP.md) for resource requirements, resume behavior, and troubleshooting.

## Repository guide

- [`submission/`](submission/) - submitted agent and candidate-handling code
- [`src/re_harness/`](src/re_harness/) - runner, Lean REPL client, Comparator integration, budgets, and artifacts
- [`sample-problems/`](sample-problems/) - the 16 supplied problems
- [`experiments/`](experiments/) - versioned plans, conditions, dispatch records, and development notes
- [`scripts/`](scripts/) - launch, control, validation, replay, and analysis utilities
- [`outputs/baseline/`](outputs/baseline/) - supplied-agent baseline artifacts
- [`docs/`](docs/) - setup, output contract, agent API, security notes, and the original prompt

Large per-run artifacts are kept on evidence branches rather than duplicated on `main`:

- `evidence/results-20260902` - primary supplied-set, replication, solo, and replay evidence
- `evidence/packet-variants-20260903` - counterfactual packet-variant replay evidence

Evidence cells include `result.json`, `events.jsonl`, `transcript.json`, `solution.lean`, and provenance metadata. The experimental directories on `main` record how those cells were configured and dispatched.

## AI assistance

OpenAI Codex and Claude assisted with implementation, orchestration, analysis, figures, and drafting using repository access. The work was conducted under continuous human supervision: I repeatedly inspected intermediate outputs, requested explanations, redirected or interrupted agent work, overrode proposed decisions, and revised both the experimental and narrative direction. Agents had greater autonomy over individual coding operations and first-pass prose; I retained responsibility for the research question, experimental conditions, promotion gates, interpretations, claims, and final text.
