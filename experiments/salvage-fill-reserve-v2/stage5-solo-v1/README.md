# Stage 5 same-substrate solo control

This frozen 32-cell study runs each of the 16 public problems at seed 1729
under `qwen-solo-plus` and `gptoss-solo-plus`. Each arm uses exactly one model
while retaining the C0+ prompts, deterministic tactic cascade, repair and
restart logic, salvage, verification, limits, and accounting. Collaboration is
disabled and no peer call is reserved.

The study is queued on workers 1–8 only after the last Wave D cell dispatches.
No solo cell is a substitute or retry for a Wave D cell.
