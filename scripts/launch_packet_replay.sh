#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 4 ]]; then
  echo "usage: $0 ENV_FILE PYTHON CHECKOUT OUTPUT_DIR" >&2
  exit 2
fi

env_file=$1
python_bin=$2
checkout=$3
output_dir=$4

set -a
# shellcheck disable=SC1090
source "$env_file"
set +a

exec "$python_bin" "$checkout/scripts/run_packet_replay.py" run \
  --manifest "$checkout/experiments/analysis/packet-replay-manifest.json" \
  --output-dir "$output_dir" \
  --concurrency 4
