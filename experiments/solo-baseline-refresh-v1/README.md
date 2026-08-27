# Solo baseline refresh v1

This evidence refresh reruns the two supplied solo baselines on the stable
DigitalOcean infrastructure. It does not modify the supplied baseline agent.
The manifests pin the byte hash of `baselines/simple_agent.py`, all behavioral
parameters, the full sample manifest, the upstream provider-accounting fix,
and the Lean image.

The two conditions execute sequentially on one host. Each condition uses two
outer problem workers (`--n-workers 2`), so the 8 GB host never runs more than
the previously tested two-worker load. Qwen runs first and GPT-OSS second.
Provider failures, timeouts, and `cost_unknown` remain outcomes rather than
reasons for an automatic paid retry.
