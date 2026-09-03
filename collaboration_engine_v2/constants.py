"""Frozen identifiers and matrix membership for collaboration engine v2."""

from re_harness.models import MODEL_A, MODEL_B

DESIGN_ID = "collaboration-engine-v2"
MODELS = (MODEL_A, MODEL_B)
# Experiment-dispatch definition; never read by the agent runtime.
CONDITIONS = ("c0", "c1", "c2")
# Experiment-dispatch definition; never read by the agent runtime.
CORE_PROBLEMS = (
    "p03_sq_ge_two_ab", "p06_pow_mod", "p07_least_divisible",
    "p10_factorial_pow", "putnam_2020_a2", "rmo_2000_2",
)
# Experiment-dispatch definition; never read by the agent runtime.
DEEP_PROBLEMS = ("p09_imo1964", "rmo_2000_2")
# Experiment-dispatch definition; never read by the agent runtime.
DATASET_DEFECTS = ("rmo_2000_6",)
