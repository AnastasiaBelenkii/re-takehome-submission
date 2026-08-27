"""Dependency-free constants shared by pilot agents and operations tools."""

DESIGN_ID = "uplift-pilot-v1"
MODEL_A = "qwen/qwen3.5-flash-02-23"
MODEL_B = "openai/gpt-oss-120b"
ALLOWED_MODELS = frozenset({MODEL_A, MODEL_B})
