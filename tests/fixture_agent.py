from __future__ import annotations

import asyncio
import time

from re_harness import AgentResult


class FixtureAgent:
    async def solve(self, problem, services):
        await asyncio.sleep(float(problem.metadata.get("sleep_s", 0)))
        return AgentResult(problem.challenge.replace("  sorry", "  linarith"))


def create_agent():
    return FixtureAgent()


class VerificationAgent:
    async def solve(self, problem, services):
        solution = problem.challenge.replace("  sorry", "  linarith")
        warm = await services.lean.check_file(solution)
        verification = await services.verify(solution) if warm.accepted else {"passed": False}
        warm_after_verification = await services.lean.check_file(solution)
        return AgentResult(solution, {
            "warm_accepted": warm.accepted,
            "warm_after_verification_accepted": warm_after_verification.accepted,
            "fresh_verification": dict(verification),
        })


def create_verification_agent():
    return VerificationAgent()


class CheckpointCrashAgent:
    async def solve(self, problem, services):
        services.checkpoint(problem.challenge.replace("  sorry", "  linarith"))
        raise RuntimeError("intentional crash after checkpoint")


def create_checkpoint_crash_agent():
    return CheckpointCrashAgent()


class HardHangAfterCheckpointAgent:
    async def solve(self, problem, services):
        services.checkpoint(problem.challenge.replace("  sorry", "  linarith"))
        time.sleep(60)


def create_hard_hang_agent():
    return HardHangAfterCheckpointAgent()
