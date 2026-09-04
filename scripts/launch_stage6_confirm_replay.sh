#!/bin/sh
set -eu

repo=/opt/stage6-pusher/repo
archive=$repo/evidence/archives/stage6-confirm-20260903
runroot=/opt/stage6-confirm-replay-20260903
manifest=$runroot/manifest.json
worker9=worker9

test ! -e "$runroot/launched"
python3 "$repo/scripts/build_stage6_confirm_replay_manifest.py" --archive "$archive" --output "$manifest"
sources=$(jq '.records | length' "$manifest")

# Worker 9 is first contacted only after the C1+ terminal gate invokes this script.
runtime=$(ssh "$worker9" 'for d in /opt/sfrv2-stage5-band4-d43af01-20260903/checkout /opt/stage6-pusher/runtime; do if test -x "$d/.venv/bin/python" -a -f "$d/.env"; then printf "%s\n" "$d"; exit 0; fi; done; exit 1')
ssh "$worker9" "test ! -e '$runroot/output/result.json' && mkdir -p '$runroot/output'"
scp -q "$manifest" "$worker9:$manifest"
scp -q "$repo/scripts/run_packet_replay_a2.py" "$worker9:$runtime/scripts/run_packet_replay_confirm.py"
ssh "$worker9" "tmux new-session -d -s stage6_confirm_replay 'cd $runtime && set -a && . ./.env && set +a && exec .venv/bin/python scripts/run_packet_replay_confirm.py --manifest $manifest --output-dir $runroot/output --concurrency 4 >> $runroot/replay.log 2>&1'"
touch "$runroot/launched"
stamp=$(TZ=America/Los_Angeles date '+%H:%M PT')
printf '%s\n' "- $stamp — confirm replay launched on worker 9: $sources source requests, $((sources * 16)) reissues, \$3 cap." >> "$repo/experiments/stage6-expanded/LOG.md"
