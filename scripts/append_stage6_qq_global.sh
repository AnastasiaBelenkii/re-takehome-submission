#!/bin/sh
set -eu

repo=/opt/stage6-pusher/repo
base_runtime=/opt/sfrv2-stage5-band4-d43af01-20260903/checkout
global=/opt/stage6-confirm-20260903/global
state=$global/global-controller-state.json
queue=$global/global-queue.json
combined=$global/global-queue-with-qq.json
archive=evidence/archives/stage6-confirm-20260903

test -f "$state"
test -f "$queue"
test ! -e "$global/qq-appended"
test "$(jq '[.tasks[] | select(.status == "dispatching")] | length' "$state")" = 0

cd "$repo"
GIT_ASKPASS=/root/stage6_git_askpass.sh GIT_TERMINAL_PROMPT=0 git fetch -q origin refs/heads/qq-arm-v1
sha=$(git rev-parse FETCH_HEAD)
gate=$(git show "$sha:experiments/stage6-expanded/QQ_GATE.md")
printf '%s\n' "$gate" | grep -Eq '^Status: \*\*PASSED\*\*[[:space:]]*$'
short=$(printf '%.12s' "$sha")
runtime="/opt/sfrv2-qq-arm-v1-$short/checkout"

stage=$(mktemp -d /opt/stage6-qq-runtime.XXXXXX)
trap 'rm -rf "$stage"' EXIT
git archive "$sha" | tar -x -C "$stage"
cp -a "$base_runtime/sample-problems/manifest.json" "$stage/sample-problems/manifest.json"
for problem in aime_1983_p1 aime_1990_p4 algebra_amgm_sumasqdivbgeqsuma aime_1990_p15 aime_1997_p9 algebra_others_exirrpowirrrat algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7 algebra_9onxpypzleqsum2onxpy
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
    test -e "$runtime/.venv" || ln -s "$base_runtime/.venv" "$runtime/.venv"
    test -e "$runtime/.env" || { test ! -f "$base_runtime/.env" || ln -s "$base_runtime/.env" "$runtime/.env"; }
  else
    scp -q "$tarball" "$target:/opt/stage6-qq-runtime-$short.tar"
    ssh "$target" "mkdir -p '$runtime' && tar -C '$runtime' -xf '/opt/stage6-qq-runtime-$short.tar' && test -e '$runtime/.venv' || ln -s '$base_runtime/.venv' '$runtime/.venv'; test -e '$runtime/.env' || { test ! -f '$base_runtime/.env' || ln -s '$base_runtime/.env' '$runtime/.env'; }"
  fi
}
install_runtime local
for target in root@10.122.0.4 root@10.122.0.3 root@10.122.0.5 root@10.122.0.7 root@10.122.0.6 root@10.122.0.8 root@10.122.0.10 root@10.122.0.11
do
  install_runtime "$target"
done

qqdir=$global/qq-descriptors
mkdir -p "$qqdir"
python3 - "$queue" "$combined" "$qqdir" "$sha" <<'PY'
import json, sys
from datetime import datetime, timezone
from pathlib import Path
old_queue, combined, qqdir = map(Path, sys.argv[1:4])
sha = sys.argv[4]
queue = json.loads(old_queue.read_text())
if len(queue["descriptors"]) != 128:
    raise SystemExit("primary queue is not the frozen 128-cell queue")
problems = ["aime_1983_p1","aime_1990_p4","algebra_amgm_sumasqdivbgeqsuma","aime_1990_p15","aime_1997_p9","algebra_others_exirrpowirrrat","algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7","algebra_9onxpypzleqsum2onxpy"]
paths = list(queue["descriptors"])
resources = {"budget_usd":1,"comparator_timeout_s":420,"diagnostic_chars":6000,"dispatch_cutoff_s":960,"failure_memory_chars":3000,"fast_track_reserved_calls":0,"generation_max_tokens":12000,"lean_check_timeout_s":120,"max_calls_per_model":25,"max_cost_free_429_retries":2,"max_restarts":2,"model_call_wall_timeout_s":420,"outer_time_s":2100,"peer_packet_chars":6000,"reserve_release_margin_s":120,"salvage_check_timeout_s":2,"temperature":0.2,"verify_reserve_s":480}
stamp = datetime.now(timezone.utc).isoformat()
for offset, (seed, problem) in enumerate(( (seed, problem) for seed in (8101,8102,8103,8104) for problem in problems )):
    index = 128 + offset
    task_id = f"stage6-confirm-qq-{problem}-s{seed}-c0-qq"
    descriptor = {"schema_version":1,"experiment":"stage6-expanded-confirm-v1-global-fifo","git_commit":sha,"prepared_at":stamp,"not_before":stamp,"worker":"assigned-at-dispatch","resources":resources,"task":{"task_id":task_id,"stage":"stage6-confirm-qq","analysis_set":"same_model_portfolio_control","block_id":f"{problem}-s{seed}","problem":problem,"seed":seed,"condition":"c0-qq","strategy":"none","profile":"shallow","dispatch_index":index}}
    path = qqdir / f"{index:03d}-{task_id}.json"
    path.write_text(json.dumps(descriptor, indent=2, sort_keys=True) + "\n")
    paths.append(str(path.resolve()))
queue["descriptors"] = paths
queue["experiment"] = "stage6-expanded-confirm-v1-global-fifo-with-qq"
combined.write_text(json.dumps(queue, indent=2, sort_keys=True) + "\n")
PY

pid=$(pgrep -f 'run_stage6_global_queue.py.*stage6-confirm-20260903/global/global-queue.json' | head -1 || true)
test -n "$pid"
kill -STOP "$pid"
sleep 1
test "$(jq '[.tasks[] | select(.status == "dispatching")] | length' "$state")" = 0
kill -TERM "$pid"
kill -CONT "$pid"
for i in 1 2 3 4 5; do kill -0 "$pid" 2>/dev/null || break; sleep 1; done
! kill -0 "$pid" 2>/dev/null

python3 - "$state" "$combined" <<'PY'
import json, sys
from datetime import datetime, timezone
from pathlib import Path
state_path, queue_path = map(Path, sys.argv[1:])
state = json.loads(state_path.read_text())
queue = json.loads(queue_path.read_text())
ids = [json.loads(Path(path).read_text())["task"]["task_id"] for path in queue["descriptors"]]
if state["task_ids"] != ids[:128]:
    raise SystemExit("primary queue changed; refusing append")
for task_id in ids[128:]:
    state["task_ids"].append(task_id)
    state["tasks"][task_id] = {"status":"pending"}
state["updated_at"] = datetime.now(timezone.utc).isoformat()
tmp = state_path.with_suffix(".tmp")
tmp.write_text(json.dumps(state, indent=2, sort_keys=True) + "\n")
tmp.replace(state_path)
PY

stamp=$(TZ=America/Los_Angeles date '+%H:%M PT')
cat >> "$repo/experiments/stage6-expanded/CONFIRM_PLAN.md" <<EOF

## Real same-model portfolio control (appended after primary queue)

Part A gate: **PASSED** on branch `qq-arm-v1`, SHA `$sha`. The 32 `c0-qq`
cells are appended after all 128 frozen primary descriptors, preserving every
already-queued descriptor and global order. They use seeds 8101–8104 and the same
eight confirm-study problems; both tracks are Qwen with explicit IDs `qwen#1` and
`qwen#2`, silent communication, and no reserved call.

Prediction: H1 is that the c0-qq rate lies within ±0.05 of `1 − (1 − p_Q)²` from
the same-block qwen-solo-plus cells. A larger deficit indicates correlated Qwen draws;
a larger surplus indicates an effect beyond independent sampling.
EOF
printf '%s\n' "- $stamp — qq arm launched ${stamp% PT}, 32 cells, SHA $sha." >> "$repo/experiments/stage6-expanded/LOG.md"
touch "$global/qq-appended"
cd "$repo"
git add experiments/stage6-expanded/CONFIRM_PLAN.md experiments/stage6-expanded/LOG.md scripts/run_stage6_global_queue.py scripts/push_stage6_confirm.py scripts/append_stage6_qq_global.sh
git commit -m "Archive root $archive; 0 c0-qq cells appended; passes per arm: c0-qq 0/0"
GIT_ASKPASS=/root/stage6_git_askpass.sh GIT_TERMINAL_PROMPT=0 git push origin HEAD:evidence/results-20260902

tmux new-session -d -s stage6_confirm_controller \
  "cd $repo && exec python3 scripts/run_stage6_global_queue.py --queue $combined --state $state --remote-root $global --runtime $base_runtime --runtime-by-condition '{\"c0-qq\": \"$runtime\"}' --session stage6_confirm_cell --hosts marketplace worker2 worker3 worker4 worker5 worker6 worker7 worker8 worker10 >> $global/controller.log 2>&1"
echo "qq arm launched ${stamp% PT}, 32 cells, SHA $sha"
