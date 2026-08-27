# Collaboration engine v1

This experiment holds the two-model H+D solve engine fixed and varies only an
information-sharing strategy. `hd-none` emits no packets. `hd-reciprocal`
symmetrically supplies each model's failed first candidate and diagnostics to the
other model's next already-scheduled repair call.

The shared engine exclusively owns model-call scheduling, call ceilings, retries,
Lean checks, diagnostics, restarts, checkpoints, stopping, and selection. A
strategy sees frozen post-check observations and can return only validated,
bounded peer packets. It cannot access `Services` or mutable track state. Thus a
new information-sharing design is one strategy class plus a registry entry; it
does not fork the uplift implementation.

This boundary intentionally does **not** cover collaboration designs that add
calls, change model allocation, vote, or delegate subproblems. Those belong to a
separate resource-allocation experiment family and must not be compared as if
they differed only in communication.

Both checked-in conditions use the full 16-problem sample set and the identical
resource manifest. The only treatment cost not matched is the extra input tokens
in the bounded peer packet; actual calls, tokens, cost, and latency must be
reported.

Model-visible common state is limited to the problem, pristine challenge,
attempt/phase, own current candidate, own Lean diagnostics, and bounded failed
trajectory content. The treatment adds only the peer packet. Condition names,
strategy names, and artifact hashes are recorded in metadata but never prompted.

Run a non-mutating launch check with:

```bash
python scripts/launch_collaboration_condition.py \
  experiments/collaboration-engine-v1/conditions/hd-none.json --check
```
