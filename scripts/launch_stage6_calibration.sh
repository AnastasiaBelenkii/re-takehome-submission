#!/bin/sh
set -eu

repo=/opt/stage6-pusher/repo
runtime=/opt/sfrv2-stage5-band4-d43af01-20260903/checkout
root=/opt/stage6-calibration-20260903

hour=$(TZ=America/Los_Angeles date +%H)
if [ "$hour" -ge 14 ]; then
  echo "refusing calibration launch at or after 14:00 PT" >&2
  exit 4
fi
if ! grep -q 'replay-k8 pushed:' "$repo/experiments/stage6-expanded/LOG.md"; then
  echo "A2 final push is not present; calibration remains gated" >&2
  exit 3
fi

tmux has-session -t stage6_calibration_pusher 2>/dev/null ||
  tmux new-session -d -s stage6_calibration_pusher \
    "cd $repo && GIT_ASKPASS=/root/stage6_git_askpass.sh GIT_TERMINAL_PROMPT=0 python3 scripts/push_stage6_calibration.py >> /opt/stage6-pusher/calibration-pusher.log 2>&1"

index=1
for host in marketplace worker2 worker3 worker4 worker5 worker6 worker7 worker8; do
  ssh "$host" "
    test ! -e $root/worker$index/queue-state.json
    ! tmux has-session -t stage6_calibration 2>/dev/null
    tmux new-session -d -s stage6_calibration \\
      'cd $runtime && exec .venv/bin/python scripts/run_remote_microcell_queue.py --worktree $runtime --queue $root/worker$index/queue.json --run-root $root/worker$index --launch-deadline 2026-09-03T21:00:00+00:00 >> $root/worker$index/queue.log 2>&1'
  "
  index=$((index + 1))
done

echo "calibration launched: 128 fixed cells"
