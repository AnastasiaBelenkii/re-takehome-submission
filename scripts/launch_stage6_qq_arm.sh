#!/bin/sh
set -eu

repo=/opt/stage6-pusher/repo
base_runtime=/opt/sfrv2-stage5-band4-d43af01-20260903/checkout
solo_state=/opt/stage6-confirm-20260903/solo-global/global-controller-state.json
global=/opt/stage6-confirm-20260903/qq-global
archive=evidence/archives/stage6-confirm-20260903

# Part B gates: Part A passed and every solo-extension cell has dispatched.
test -f "$solo_state"
test "$(jq '[.tasks[].status == "pending"] | any' "$solo_state")" = false
test ! -e "$global/global-controller-state.json"
! tmux has-session -t stage6_confirm_qq_controller 2>/dev/null

cd "$repo"
GIT_ASKPASS=/root/stage6_git_askpass.sh GIT_TERMINAL_PROMPT=0 git fetch -q origin refs/heads/qq-arm-v1
sha=$(git rev-parse FETCH_HEAD)
gate=$(git show "$sha:experiments/stage6-expanded/QQ_GATE.md")
printf '%s\n' "$gate" | grep -Eq '(^|[^A-Z])PASSED([^A-Z]|$)'
short=$(printf '%.12s' "$sha")
runtime="/opt/sfrv2-qq-arm-v1-$short/checkout"

# Assemble the tested branch without altering the frozen Wave-D checkout.  The
# expanded statements come from the frozen Stage 6 runtime and the Python
# environment is shared read-only.
stage=$(mktemp -d /opt/stage6-qq-runtime.XXXXXX)
trap 'rm -rf "$stage"' EXIT
git archive "$sha" | tar -x -C "$stage"
for problem in \
  aime_1983_p1 aime_1990_p4 algebra_amgm_sumasqdivbgeqsuma aime_1990_p15 \
  aime_1997_p9 algebra_others_exirrpowirrrat \
  algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 \
  algebra_9onxpypzleqsum2onxpy
do
  rm -rf "$stage/sample-problems/$problem"
  cp -a "$base_runtime/sample-problems/$problem" "$stage/sample-problems/$problem"
done
tarball="/opt/stage6-qq-runtime-$short.tar"
tar -C "$stage" -cf "$tarball" .

install_runtime() {
  target=$1
  if [ "$target" = local ]; then
    mkdir -p "$runtime"
    tar -C "$runtime" -xf "$tarball"
    ln -s "$base_runtime/.venv" "$runtime/.venv"
    test ! -f "$base_runtime/.env" || ln -s "$base_runtime/.env" "$runtime/.env"
  else
    scp -q "$tarball" "$target:/opt/stage6-qq-runtime-$short.tar"
    ssh "$target" "mkdir -p '$runtime' && tar -C '$runtime' -xf '/opt/stage6-qq-runtime-$short.tar' && ln -s '$base_runtime/.venv' '$runtime/.venv' && { test ! -f '$base_runtime/.env' || ln -s '$base_runtime/.env' '$runtime/.env'; }"
  fi
}
install_runtime local
for target in root@10.122.0.4 root@10.122.0.3 root@10.122.0.5 root@10.122.0.7 root@10.122.0.6 root@10.122.0.8 root@10.122.0.10 root@10.122.0.11
do
  install_runtime "$target"
done

mkdir -p "$global/descriptors"
python3 - "$global" "$sha" <<'PY'
import json, sys
from datetime import datetime, timezone
from pathlib import Path

root, sha = Path(sys.argv[1]), sys.argv[2]
problems = [
    "aime_1983_p1", "aime_1990_p4", "algebra_amgm_sumasqdivbgeqsuma",
    "aime_1990_p15", "aime_1997_p9", "algebra_others_exirrpowirrrat",
    "algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7",
    "algebra_9onxpypzleqsum2onxpy",
]
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
for seed in (8101, 8102, 8103, 8104):
    for problem in problems:
        task_id = f"stage6-confirm-qq-{problem}-s{seed}-c0-qq"
        descriptor = {
            "schema_version": 1, "experiment": "stage6-expanded-confirm-qq-v1",
            "git_commit": sha, "prepared_at": stamp, "not_before": stamp,
            "worker": "assigned-at-dispatch", "resources": dict(resources),
            "task": {"task_id": task_id, "stage": "stage6-confirm-qq",
                     "analysis_set": "same_model_portfolio_control",
                     "block_id": f"{problem}-s{seed}", "problem": problem, "seed": seed,
                     "condition": "c0-qq", "strategy": "none", "profile": "shallow",
                     "dispatch_index": index},
        }
        path = root / "descriptors" / f"{index:03d}-{task_id}.json"
        path.write_text(json.dumps(descriptor, indent=2, sort_keys=True) + "\n")
        paths.append(str(path.resolve()))
        index += 1
assert index == 32
(root / "global-queue.json").write_text(json.dumps({
    "schema_version": 1, "experiment": "stage6-expanded-confirm-qq-v1-global-fifo",
    "order": "seed-major then frozen problem-list order", "descriptors": paths,
}, indent=2) + "\n")
PY

cat >> "$repo/experiments/stage6-expanded/CONFIRM_PLAN.md" <<EOF

## Real same-model portfolio control

Part A gate: **PASSED** on branch \`qq-arm-v1\` at \`$sha\`. After every solo-extension
cell dispatched, append 32 \`c0-qq\` cells: the same eight problems at seeds 8101–8104,
in seed-major then frozen problem order. This differs from \`d43af01\` only in the added
condition and explicit track ids; both tracks are Qwen, communication is silent, and
there is no reserved call.

Prediction frozen before launch: H1 is that \`c0-qq\` pass rate on the 32 blocks lies
within ±0.05 of \`1 - (1 - p_Q)^2\`, where \`p_Q\` is computed from the
\`qwen-solo-plus\` cells on the same blocks. More than 0.05 below indicates correlated
within-problem Qwen draws; more than 0.05 above indicates something beyond sampling
in the portfolio.
EOF
stamp=$(TZ=America/Los_Angeles date '+%H:%M PT')
printf '%s\n' "- $stamp — qq arm launched ${stamp% PT}, 32 cells, SHA $sha." >> "$repo/experiments/stage6-expanded/LOG.md"
git add experiments/stage6-expanded/CONFIRM_PLAN.md experiments/stage6-expanded/LOG.md scripts/launch_stage6_qq_arm.sh scripts/push_stage6_confirm.py
git commit -m "Archive root $archive; 0 c0-qq cells; passes per arm: c0-qq 0/0"
GIT_ASKPASS=/root/stage6_git_askpass.sh GIT_TERMINAL_PROMPT=0 git push origin HEAD:evidence/results-20260902

tmux new-session -d -s stage6_confirm_qq_controller \
  "cd $repo && exec python3 scripts/run_stage6_global_queue.py --queue $global/global-queue.json --state $global/global-controller-state.json --remote-root $global --runtime $runtime --session stage6_confirm_cell --hosts marketplace worker2 worker3 worker4 worker5 worker6 worker7 worker8 worker10 >> $global/controller.log 2>&1"

echo "qq arm launched ${stamp% PT}, 32 cells, SHA $sha"
