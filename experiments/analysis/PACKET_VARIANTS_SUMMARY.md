# Packet-content replay variants

Warm-pass outcomes count provider refusals and local-check errors as failures. Differences are paired at the request-state level against the existing K=8 `without_packet` rate for the same 47 states.

| Variant | Warm passes | Request-level mean | Paired difference | States up/down/tied |
|---|---:|---:|---:|---:|
| `lemmas_only` | 149/376 | 0.396 | -0.008 | 10/10/27 |
| `prefix_cap3` | 141/376 | 0.375 | -0.029 | 5/13/29 |

## Splits

### Wave

| Group | Variant | Warm passes | Request-level mean | Paired difference | States up/down/tied |
|---|---|---:|---:|---:|---:|
| wave_c | `lemmas_only` | 73/200 | 0.365 | -0.010 | 5/6/14 |
| wave_c | `prefix_cap3` | 66/200 | 0.330 | -0.045 | 1/9/15 |
| wave_d | `lemmas_only` | 76/176 | 0.432 | -0.006 | 5/4/13 |
| wave_d | `prefix_cap3` | 75/176 | 0.426 | -0.011 | 4/4/14 |

### Receiving model

| Group | Variant | Warm passes | Request-level mean | Paired difference | States up/down/tied |
|---|---|---:|---:|---:|---:|
| openai/gpt-oss-120b | `lemmas_only` | 53/200 | 0.265 | +0.000 | 6/8/11 |
| openai/gpt-oss-120b | `prefix_cap3` | 45/200 | 0.225 | -0.040 | 2/8/15 |
| qwen/qwen3.5-flash-02-23 | `lemmas_only` | 96/176 | 0.545 | -0.017 | 4/2/16 |
| qwen/qwen3.5-flash-02-23 | `prefix_cap3` | 96/176 | 0.545 | -0.017 | 3/5/14 |
