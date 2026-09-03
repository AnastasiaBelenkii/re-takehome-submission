#!/bin/sh
set -eu

repo=/opt/stage6-pusher/repo
runtime=/opt/sfrv2-stage5-band4-d43af01-20260903/checkout
root=/opt/stage6-pass8-20260903

hour=$(TZ=America/Los_Angeles date +%H)
if [ "$hour" -ge 14 ]; then
  echo "refusing pass@8 launch at or after 14:00 PT" >&2
  exit 4
fi
test -f "$repo/experiments/stage6-expanded/CALIBRATION.md" || {
  echo "calibration has not been pushed" >&2
  exit 3
}

tmux has-session -t stage6_pass8_pusher 2>/dev/null ||
  tmux new-session -d -s stage6_pass8_pusher \
    "cd $repo && GIT_ASKPASS=/root/stage6_git_askpass.sh GIT_TERMINAL_PROMPT=0 python3 scripts/push_stage6_pass8.py >> /opt/stage6-pusher/pass8-pusher.log 2>&1"

index=1
for host in marketplace worker2 worker3 worker4 worker5 worker6 worker7 worker8; do
  ssh "$host" "
    test ! -e $root/qwen/worker$index/queue-state.json
    ! tmux has-session -t stage6_pass8_qwen 2>/dev/null
    tmux new-session -d -s stage6_pass8_qwen \\
      'cd $runtime && exec .venv/bin/python scripts/run_remote_microcell_queue.py --worktree $runtime --queue $root/qwen/worker$index/queue.json --run-root $root/qwen/worker$index --launch-deadline 2026-09-03T21:00:00+00:00 >> $root/qwen/worker$index/queue.log 2>&1'
  "
  index=$((index + 1))
done

stamp=$(TZ=America/Los_Angeles date '+%H:%M PT')
printf '%s\n' "- $stamp — pass@8 launched at ${stamp% PT}." >> "$repo/experiments/stage6-expanded/LOG.md"
cd "$repo"
git add experiments/stage6-expanded/LOG.md
git commit -m 'Archive root evidence/archives/stage6-pass8-20260903; 0 cells; passes per arm: prelaunch'
GIT_ASKPASS=/root/stage6_git_askpass.sh GIT_TERMINAL_PROMPT=0 git push origin HEAD:evidence/results-20260902
echo "pass@8 launched at ${stamp% PT}"
