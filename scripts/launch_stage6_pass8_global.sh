#!/bin/sh
set -eu

repo=/opt/stage6-pusher/repo
runtime=/opt/sfrv2-stage5-band4-d43af01-20260903/checkout
prepared=/opt/stage6-pass8-20260903/qwen
global=/opt/stage6-pass8-20260903/global
archive=evidence/archives/stage6-pass8-20260903

clock=$(TZ=America/Los_Angeles date +%H%M)
if [ "$clock" -ge 1430 ]; then
  echo "refusing screen launch at or after 14:30 PT" >&2
  exit 4
fi
test ! -e "$global/global-controller-state.json"
! tmux has-session -t stage6_pass8_controller 2>/dev/null

mkdir -p "$global/descriptors"
index=1
for host in marketplace worker2 worker3 worker4 worker5 worker6 worker7 worker8; do
  rsync -a "$host:$prepared/worker$index/descriptors/" "$global/descriptors/"
  index=$((index + 1))
done

python3 - "$global" <<'PY'
import json, sys
from pathlib import Path
root = Path(sys.argv[1])
paths = sorted(root.joinpath("descriptors").glob("*.json"))
items = [json.loads(path.read_text()) for path in paths]
items.sort(key=lambda item: int(item["task"]["dispatch_index"]))
indices = [int(item["task"]["dispatch_index"]) for item in items]
if indices != list(range(256)):
    raise SystemExit(f"global queue is not exactly dispatch indices 0..255: {indices[:3]}...{indices[-3:]}")
queue = {
    "schema_version": 1,
    "experiment": "stage6-expanded-pass8-v1-global-fifo",
    "order": "seed-major then frozen PLAN.md order",
    "descriptors": [str(paths[indices.index(i)].resolve()) for i in range(256)],
}
root.joinpath("global-queue.json").write_text(json.dumps(queue, indent=2) + "\n")
PY

stamp=$(TZ=America/Los_Angeles date '+%H:%M PT')
printf '%s\n' "- $stamp — screen launched ${stamp% PT} on 8 workers." >> "$repo/experiments/stage6-expanded/LOG.md"
cd "$repo"
git add experiments/stage6-expanded/LOG.md scripts/run_stage6_global_queue.py scripts/launch_stage6_pass8_global.sh scripts/push_stage6_pass8.py
git commit -m "Archive root $archive; 0 cells; passes per arm: qwen-solo-plus 0/0"
GIT_ASKPASS=/root/stage6_git_askpass.sh GIT_TERMINAL_PROMPT=0 git push origin HEAD:evidence/results-20260902

tmux new-session -d -s stage6_pass8_pusher \
  "cd $repo && GIT_ASKPASS=/root/stage6_git_askpass.sh GIT_TERMINAL_PROMPT=0 python3 scripts/push_stage6_pass8.py >> /opt/stage6-pusher/pass8-pusher.log 2>&1"
tmux new-session -d -s stage6_pass8_controller \
  "cd $repo && exec python3 scripts/run_stage6_global_queue.py --queue $global/global-queue.json --state $global/global-controller-state.json --remote-root $global --runtime $runtime --session stage6_pass8_cell --hosts marketplace worker2 worker3 worker4 worker5 worker6 worker7 worker8 >> $global/controller.log 2>&1"

echo "screen launched ${stamp% PT} on 8 workers"
