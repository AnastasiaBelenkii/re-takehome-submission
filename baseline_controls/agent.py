"""Stock solo baseline with the call ceiling raised from 25 to 50."""

from __future__ import annotations

import os

from baselines.simple_agent import SimpleBaselineAgent


def create_agent() -> SimpleBaselineAgent:
    """Change only the stock agent's maximum repair-loop depth."""

    if os.environ.get("BASELINE_MAX_TURNS", "50") != "50":
        raise ValueError("the solo@50 factory requires BASELINE_MAX_TURNS=50")
    return SimpleBaselineAgent(max_turns=50)
