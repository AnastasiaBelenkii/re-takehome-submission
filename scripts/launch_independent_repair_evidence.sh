#!/usr/bin/env bash
# Launch a frozen, provenance-recorded 16-problem independent-repair run.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
EXPECTED_DESIGN="independent-repair-portfolio-v1"
PINNED_IMAGE="ghcr.io/verifiedmechanisms/re-takehome-lean@sha256:ee48287cd31c0a7df572093a879ed7289c2f01fec6c7af8716c605fc8c670c39"
EXPERIMENTS_ROOT=${EXPERIMENTS_ROOT:-/opt/experiments}
RESULTS_ROOT=${RESULTS_ROOT:-/opt/takehome-results}
CHECK_ONLY=0

usage() {
  echo "Usage: $0 [--check]"
  echo
  echo "Environment overrides:"
  echo "  EXPERIMENTS_ROOT  Frozen worktrees (default: /opt/experiments)"
  echo "  RESULTS_ROOT      Run artifacts (default: /opt/takehome-results)"
}

case ${1:-} in
  "") ;;
  --check) CHECK_ONLY=1 ;;
  -h|--help) usage; exit 0 ;;
  *) usage >&2; exit 2 ;;
esac

for command in git python3 docker nohup sha256sum; do
  command -v "$command" >/dev/null 2>&1 || {
    echo "Required command is unavailable: $command" >&2
    exit 1
  }
done
docker version >/dev/null 2>&1 || {
  echo "Docker is installed but its daemon is unavailable" >&2
  exit 1
}

cd "$ROOT"
git diff --quiet
git diff --cached --quiet
COMMIT=$(git rev-parse HEAD)
SHORT_COMMIT=${COMMIT:0:8}
SOURCE_ENV="$ROOT/.env"
test -f "$SOURCE_ENV" || {
  echo "Missing $SOURCE_ENV; configure OPENROUTER_API_KEY there first" >&2
  exit 1
}

python3 - "$SOURCE_ENV" <<'PY'
import sys
from pathlib import Path

configured = any(
    line.strip().startswith("OPENROUTER_API_KEY=")
    and line.strip().split("=", 1)[1].strip()
    for line in Path(sys.argv[1]).read_text(encoding="utf-8").splitlines()
)
if not configured:
    raise SystemExit("OPENROUTER_API_KEY is empty or absent in .env")
PY

if (( CHECK_ONLY )); then
  CHECK_PYTHON=python3
  if [[ -x "$ROOT/.venv/bin/python" ]]; then
    CHECK_PYTHON="$ROOT/.venv/bin/python"
  fi
  DESIGN=$(PYTHONPATH="$ROOT/src:$ROOT" "$CHECK_PYTHON" - <<'PY'
from submission.agent import DESIGN_ID
print(DESIGN_ID)
PY
  )
  test "$DESIGN" = "$EXPECTED_DESIGN" || {
    echo "Wrong submission design: expected $EXPECTED_DESIGN, found $DESIGN" >&2
    exit 1
  }
  echo "launcher check passed"
  echo "commit=$COMMIT"
  echo "design=$DESIGN"
  echo "image=$PINNED_IMAGE"
  exit 0
fi

LAUNCHED_AT=$(date -u +%Y%m%dT%H%M%SZ)
WORKTREE="$EXPERIMENTS_ROOT/independent-repair-$LAUNCHED_AT-$SHORT_COMMIT"
RUN_ROOT="$RESULTS_ROOT/independent-repair-$LAUNCHED_AT-$SHORT_COMMIT"
OUTPUT_ROOT="$RUN_ROOT/outputs"
LOG_PATH="$RUN_ROOT/run.log"
PID_PATH="$RUN_ROOT/run.pid"
PROVENANCE_PATH="$RUN_ROOT/provenance.json"

test ! -e "$WORKTREE" || {
  echo "Frozen worktree already exists: $WORKTREE" >&2
  echo "Refusing to reuse a potentially modified experiment directory." >&2
  exit 1
}
test ! -e "$RUN_ROOT" || {
  echo "Result directory already exists: $RUN_ROOT" >&2
  exit 1
}

mkdir -p "$EXPERIMENTS_ROOT" "$RUN_ROOT"
git worktree add --detach "$WORKTREE" "$COMMIT"
cp --preserve=mode "$SOURCE_ENV" "$WORKTREE/.env"
chmod 600 "$WORKTREE/.env"

(
  cd "$WORKTREE"
  LEAN_IMAGE="$PINNED_IMAGE" bash scripts/setup.sh
)

DESIGN=$(PYTHONPATH="$WORKTREE/src:$WORKTREE" "$WORKTREE/.venv/bin/python" - <<'PY'
from submission.agent import DESIGN_ID
print(DESIGN_ID)
PY
)
test "$DESIGN" = "$EXPECTED_DESIGN" || {
  echo "Wrong frozen submission design: expected $EXPECTED_DESIGN, found $DESIGN" >&2
  exit 1
}

SCRIPT_SHA256=$(sha256sum "$WORKTREE/scripts/launch_independent_repair_evidence.sh" | awk '{print $1}')
"$WORKTREE/.venv/bin/python" - \
  "$PROVENANCE_PATH" "$COMMIT" "$SCRIPT_SHA256" "$LAUNCHED_AT" \
  "$WORKTREE" "$OUTPUT_ROOT" "$PINNED_IMAGE" "$DESIGN" <<'PY'
import json
import os
import platform
import socket
import sys
from pathlib import Path

(
    destination,
    commit,
    script_sha256,
    launched_at,
    worktree,
    output_root,
    lean_image,
    design_id,
) = sys.argv[1:]

settings = {
    "VM_TIME_LIMIT_S": "1200",
    "VM_BUDGET_USD": "1.00",
    "VM_VERIFY_RESERVE_S": "120",
    "LEAN_CHECK_TIMEOUT_S": "120",
    "COMPARATOR_TIMEOUT_S": "180",
    "BASELINE_MAX_TURNS": "25",
    "BASELINE_MAX_TOKENS": "12000",
    "BASELINE_TEMPERATURE": "0.2",
    "n_workers": 1,
}
command = [
    str(Path(worktree) / ".venv/bin/python"),
    str(Path(worktree) / "run.py"),
    "--problems",
    str(Path(worktree) / "sample-problems"),
    "--out",
    output_root,
    "--n-workers",
    "1",
]
memory_kib = None
try:
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemTotal:"):
            memory_kib = int(line.split()[1])
            break
except OSError:
    pass

payload = {
    "schema_version": 1,
    "experiment": "independent-repair-evidence",
    "design_id": design_id,
    "launched_at": launched_at,
    "git_commit": commit,
    "launcher_sha256": script_sha256,
    "worktree": worktree,
    "output_root": output_root,
    "command": command,
    "environment": settings,
    "lean_image": lean_image,
    "models": ["qwen/qwen3.5-flash-02-23", "openai/gpt-oss-120b"],
    "host": {
        "hostname": socket.gethostname(),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "cpu_count": os.cpu_count(),
        "memory_total_kib": memory_kib,
    },
}
Path(destination).write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
PY

mkdir -p "$OUTPUT_ROOT"
nohup env \
  LEAN_IMAGE="$PINNED_IMAGE" \
  VM_TIME_LIMIT_S=1200 \
  VM_BUDGET_USD=1.00 \
  VM_VERIFY_RESERVE_S=120 \
  LEAN_CHECK_TIMEOUT_S=120 \
  COMPARATOR_TIMEOUT_S=180 \
  BASELINE_MAX_TURNS=25 \
  BASELINE_MAX_TOKENS=12000 \
  BASELINE_TEMPERATURE=0.2 \
  "$WORKTREE/.venv/bin/python" "$WORKTREE/run.py" \
  --problems "$WORKTREE/sample-problems" \
  --out "$OUTPUT_ROOT" \
  --n-workers 1 \
  >"$LOG_PATH" 2>&1 </dev/null &
RUN_PID=$!
echo "$RUN_PID" >"$PID_PATH"

for _ in $(seq 1 30); do
  if ! kill -0 "$RUN_PID" 2>/dev/null; then
    echo "Run exited during startup; log follows:" >&2
    tail -n 100 "$LOG_PATH" >&2 || true
    exit 1
  fi
  if find "$OUTPUT_ROOT" -name run.json -print -quit | grep -q .; then
    echo "evidence run launched"
    echo "pid=$RUN_PID"
    echo "commit=$COMMIT"
    echo "worktree=$WORKTREE"
    echo "run_root=$RUN_ROOT"
    echo "log=$LOG_PATH"
    echo "provenance=$PROVENANCE_PATH"
    exit 0
  fi
  sleep 1
done

echo "Run remains alive but run.json was not observed within 30 seconds." >&2
echo "Inspect $LOG_PATH before relying on it." >&2
exit 1
