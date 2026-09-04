#!/bin/sh
set -eu

repo=/opt/stage6-pusher/repo
runtime=/opt/sfrv2-stage5-band4-d43af01-20260903/checkout
primary=/opt/stage6-confirm-20260903/global/global-controller-state.json
global=/opt/stage6-confirm-20260903/solo-global
archive=evidence/archives/stage6-confirm-20260903

test "$(jq '[.tasks[].status == "pending"] | any' "$primary")" = false
test ! -e "$global/global-controller-state.json"
! tmux has-session -t stage6_confirm_solo_controller 2>/dev/null
mkdir -p "$global/descriptors"

python3 - "$global" <<'PY'
import json, sys
from datetime import datetime, timezone
from pathlib import Path

root = Path(sys.argv[1])
problems = [
    "aime_1983_p1",
    "aime_1990_p4",
    "algebra_amgm_sumasqdivbgeqsuma",
    "aime_1990_p15",
    "aime_1997_p9",
    "algebra_others_exirrpowirrrat",
    "algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7",
    "algebra_9onxpypzleqsum2onxpy",
]
arms = ["qwen-solo-plus", "gptoss-solo-plus"]
resources = {
    "budget_usd": 1, "comparator_timeout_s": 420, "diagnostic_chars": 6000,
    "dispatch_cutoff_s": 960, "failure_memory_chars": 3000,
    "fast_track_reserved_calls": 0, "generation_max_tokens": 12000,
    "lean_check_timeout_s": 120, "max_calls_per_model": 25,
    "max_cost_free_429_retries": 2, "max_restarts": 2,
    "model_call_wall_timeout_s": 420, "outer_time_s": 2100,
    "peer_packet_chars": 6000, "reserve_release_margin_s": 120,
    "salvage_check_timeout_s": 2, "temperature": 0.2, "verify_reserve_s": 480,
}
paths, index = [], 0
stamp = datetime.now(timezone.utc).isoformat()
for seed in (8105, 8106, 8107, 8108):
    for problem in problems:
        for arm in arms:
            task_id = f"stage6-confirm-solo-{problem}-s{seed}-{arm}"
            descriptor = {
                "schema_version": 1, "experiment": "stage6-expanded-confirm-solo-v1",
                "git_commit": "d43af0199db14b36e1761efc641aa00c2dbc3ffe",
                "prepared_at": stamp, "not_before": stamp, "worker": "assigned-at-dispatch",
                "resources": dict(resources),
                "task": {"task_id": task_id, "stage": "stage6-confirm-solo",
                         "analysis_set": "solo_extension_virtual_portfolio",
                         "block_id": f"{problem}-s{seed}", "problem": problem, "seed": seed,
                         "condition": arm, "strategy": "none", "profile": "shallow",
                         "dispatch_index": index},
            }
            path = root / "descriptors" / f"{index:03d}-{task_id}.json"
            path.write_text(json.dumps(descriptor, indent=2, sort_keys=True) + "\n")
            paths.append(str(path.resolve()))
            index += 1
assert index == 64
(root / "global-queue.json").write_text(json.dumps({
    "schema_version": 1, "experiment": "stage6-expanded-confirm-solo-v1-global-fifo",
    "order": "seed-major, problem-list order, adjacent two-arm blocks", "descriptors": paths,
}, indent=2) + "\n")
PY

stamp=$(TZ=America/Los_Angeles date '+%H:%M PT')
printf '%s\n' "- $stamp — solo extension launched ${stamp% PT}, 64 cells." >> "$repo/experiments/stage6-expanded/LOG.md"
cd "$repo"
git add experiments/stage6-expanded/CONFIRM_PLAN.md experiments/stage6-expanded/LOG.md scripts/launch_stage6_solo_extension.sh scripts/push_stage6_confirm.py
git commit -m "Archive root $archive; 0 solo-extension cells; passes per arm: qwen-solo-plus 0/0, gptoss-solo-plus 0/0"
GIT_ASKPASS=/root/stage6_git_askpass.sh GIT_TERMINAL_PROMPT=0 git push origin HEAD:evidence/results-20260902

tmux new-session -d -s stage6_confirm_solo_controller \
  "cd $repo && exec python3 scripts/run_stage6_global_queue.py --queue $global/global-queue.json --state $global/global-controller-state.json --remote-root $global --runtime $runtime --session stage6_confirm_cell --hosts marketplace worker2 worker3 worker4 worker5 worker6 worker7 worker8 worker10 >> $global/controller.log 2>&1"

echo "solo extension launched ${stamp% PT}, 64 cells"
