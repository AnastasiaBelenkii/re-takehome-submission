# Salvage fill packets with a matched call reserve

## Decision being tested

The previous hard wave showed that `C1+` rarely exposed the fast Qwen track to
peer progress: only one of 24 C1+ model calls consumed a packet, and a better
GPT skeleton arrived after Qwen had exhausted its four calls. This iteration
does not modify the frozen `C0+`/`C1+` conditions. It adds a new matched pair:

| Condition | Within-track logic | Cross-track logic | Qwen reserve |
| --- | --- | --- | ---: |
| `c0plus-reserve` | compiler-grounded salvage | none | one of eight calls |
| `c1plus-fill-reserve` | identical salvage | latest-wins progress packets | one of eight calls |

Both arms have the same total calls, models, reasoning effort, budgets,
timeouts, and one-call Qwen reserve. In the treatment, a pending packet unlocks
the reserved call. In the control, the idle reserve releases only when GPT has
exhausted its calls or 120 seconds remain before the dispatch cutoff. Thus the
treatment receives neither an extra model call nor a looser deadline.

The C1++ receiver prompt assigns one concrete task: preserve the peer's
warm-compiling skeleton and fill every explicit `sorry` hole. It removes the
generic "critically evaluate" framing used by C1+.

## Stages and gates

1. **Offline scheduler and prompt replay.** Prove deterministically that the
   final Qwen call is held, a GPT packet unlocks it, the packet is present in
   the request, and the matched control releases only after GPT exhaustion.
2. **Pinned-Lean compatibility.** Run the full test suite and real Docker
   integration checks. The final fresh Comparator remains authoritative.
3. **Matched paid canary.** Run `putnam_2020_a2`, seed 3141, one replicate of
   each arm, concurrently on two freshly available workers. This is the prior
   wave's only seed that generated packets. Use eight calls/model, $0.25/cell,
   1,800 seconds outer time, 1,200 seconds dispatch cutoff, 240 seconds of
   verification reserve, 180-second Comparator timeout, two-second salvage
   checks, and a 420-second semantic-call deadline.
4. **Medium wave only if earned.** Expand to two or three hard problems and
   three seeds only if the canary demonstrates packet production, delivery,
   consumption, and either improved compiler-grounded progress or a verified
   solve. A treatment that still does not activate is redesigned, not scaled.
5. **Larger wave only after the medium gate.** Preserve paired blocks and
   report score together with the complete causal funnel.

## Canary outcomes

The primary canary outcome is mechanism activation, not a noisy 0/1 score:

`produced -> queued -> consumed on reserved call -> acted on -> survived Lean`

The result bundle must also retain exact requests, responses, candidates,
salvage events, packet timestamps and hashes, cost accounting, final Comparator
status, frozen source SHA, worker, and launch descriptor. A score difference is
descriptive unless the packet trace supports a causal interpretation.

## Stop conditions

Stop before the medium wave if either arm has incomplete accounting, a final
Comparator failure in the execution path, a worker collision, or a substrate
regression. Stop or redesign C1++ if no packet is consumed, if the fill prompt
is ignored, or if the packet-exposed candidate loses rather than preserves the
compiler-validated structure.
