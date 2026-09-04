#!/bin/sh
set -eu

repo=/opt/stage6-pusher/repo
runtime=/opt/sfrv2-stage5-band4-d43af01-20260903/checkout
global=/opt/stage6-confirm-20260903/global
archive=evidence/archives/stage6-confirm-20260903

test ! -e "$global/global-controller-state.json"
! tmux has-session -t stage6_confirm_controller 2>/dev/null
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
arms = ["qwen-solo-plus", "gptoss-solo-plus", "c0plus-reserve", "c1plus-fill-reserve"]
seeds = [8101, 8102, 8103, 8104]
resources = {
    "budget_usd": 1,
    "comparator_timeout_s": 420,
    "diagnostic_chars": 6000,
    "dispatch_cutoff_s": 960,
    "failure_memory_chars": 3000,
    "fast_track_reserved_calls": 0,
    "generation_max_tokens": 12000,
    "lean_check_timeout_s": 120,
    "max_calls_per_model": 25,
    "max_cost_free_429_retries": 2,
    "max_restarts": 2,
    "model_call_wall_timeout_s": 420,
    "outer_time_s": 2100,
    "peer_packet_chars": 6000,
    "reserve_release_margin_s": 120,
    "salvage_check_timeout_s": 2,
    "temperature": 0.2,
    "verify_reserve_s": 480,
}
paths = []
index = 0
stamp = datetime.now(timezone.utc).isoformat()
for seed in seeds:
    for problem in problems:
        for arm in arms:
            task_id = f"stage6-confirm-{problem}-s{seed}-{arm}"
            item_resources = dict(resources)
            if arm in {"c0plus-reserve", "c1plus-fill-reserve"}:
                item_resources["fast_track_reserved_calls"] = 1
            descriptor = {
                "schema_version": 1,
                "experiment": "stage6-expanded-confirm-v1",
                "git_commit": "d43af0199db14b36e1761efc641aa00c2dbc3ffe",
                "prepared_at": stamp,
                "not_before": stamp,
                "worker": "assigned-at-dispatch",
                "resources": item_resources,
                "task": {
                    "task_id": task_id,
                    "stage": "stage6-confirm",
                    "analysis_set": "confirm_primary_itt",
                    "block_id": f"{problem}-s{seed}",
                    "problem": problem,
                    "seed": seed,
                    "condition": arm,
                    "strategy": "progress-fill-event-latest-v2" if arm == "c1plus-fill-reserve" else "none",
                    "profile": "shallow",
                    "dispatch_index": index,
                },
            }
            path = root / "descriptors" / f"{index:03d}-{task_id}.json"
            path.write_text(json.dumps(descriptor, indent=2, sort_keys=True) + "\n")
            paths.append(str(path.resolve()))
            index += 1
assert index == 128
(root / "global-queue.json").write_text(json.dumps({
    "schema_version": 1,
    "experiment": "stage6-expanded-confirm-v1-global-fifo",
    "order": "seed-major, problem-list order, adjacent four-arm blocks",
    "descriptors": paths,
}, indent=2) + "\n")
PY

stamp=$(TZ=America/Los_Angeles date '+%H:%M PT')
printf '%s\n' "- $stamp — confirm launched ${stamp% PT}, 128 cells." >> "$repo/experiments/stage6-expanded/LOG.md"
cd "$repo"
git add experiments/stage6-expanded/CONFIRM_PLAN.md experiments/stage6-expanded/LOG.md scripts/launch_stage6_confirm_global.sh scripts/push_stage6_confirm.py
git commit -m "Archive root $archive; 0 cells; passes per arm: qwen-solo-plus 0/0, gptoss-solo-plus 0/0, c0plus-reserve 0/0, c1plus-fill-reserve 0/0"
GIT_ASKPASS=/root/stage6_git_askpass.sh GIT_TERMINAL_PROMPT=0 git push origin HEAD:evidence/results-20260902

tmux new-session -d -s stage6_confirm_pusher \
  "cd $repo && GIT_ASKPASS=/root/stage6_git_askpass.sh GIT_TERMINAL_PROMPT=0 exec python3 scripts/push_stage6_confirm.py >> /opt/stage6-pusher/confirm-pusher.log 2>&1"
tmux new-session -d -s stage6_confirm_controller \
  "cd $repo && exec python3 scripts/run_stage6_global_queue.py --queue $global/global-queue.json --state $global/global-controller-state.json --remote-root $global --runtime $runtime --session stage6_confirm_cell --hosts marketplace worker2 worker3 worker4 worker5 worker6 worker7 worker8 worker10 >> $global/controller.log 2>&1"

echo "confirm launched ${stamp% PT}, 128 cells"
