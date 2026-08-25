#!/usr/bin/env bash
# Provision an Ubuntu 22.04 Docker Droplet and launch the short accountability run.
set -euo pipefail

cd "$(dirname "$0")/.."
ROOT=$PWD

if [ "$(id -u)" -ne 0 ]; then
  echo "Run this script as root on the disposable Droplet." >&2
  exit 1
fi

export DEBIAN_FRONTEND=noninteractive
apt-get update -qq
apt-get install -y -qq git software-properties-common

if ! command -v docker >/dev/null 2>&1; then
  apt-get install -y -qq docker.io
  systemctl enable --now docker
fi
docker version >/dev/null

python_ok=false
if command -v python3 >/dev/null 2>&1 && python3 - <<'PY' >/dev/null 2>&1
import sys
raise SystemExit(0 if sys.version_info >= (3, 11) else 1)
PY
then
  python_ok=true
fi

SETUP_PATH=$PATH
if [ "$python_ok" != true ]; then
  if ! command -v python3.11 >/dev/null 2>&1; then
    add-apt-repository -y ppa:deadsnakes/ppa
    apt-get update -qq
  fi
  apt-get install -y -qq python3.11 python3.11-venv
  mkdir -p "$ROOT/.deadline-bin"
  ln -sfn "$(command -v python3.11)" "$ROOT/.deadline-bin/python3"
  SETUP_PATH="$ROOT/.deadline-bin:$PATH"
  if [ -x .venv/bin/python ] && ! .venv/bin/python - <<'PY' >/dev/null 2>&1
import sys
raise SystemExit(0 if sys.version_info >= (3, 11) else 1)
PY
  then
    mv .venv ".venv.pre-python311.$(date -u +%Y%m%dT%H%M%SZ)"
  fi
fi

PATH="$SETUP_PATH" bash scripts/setup.sh

if ! PATH="$SETUP_PATH" .venv/bin/python - <<'PY' >/dev/null 2>&1
from re_harness.config import HarnessSettings
raise SystemExit(0 if HarnessSettings.from_env(n_workers=1).api_key else 1)
PY
then
  read -r -s -p "OpenRouter API key: " OPENROUTER_KEY
  echo
  if [ -z "$OPENROUTER_KEY" ]; then
    echo "The API key cannot be empty." >&2
    exit 1
  fi
  umask 077
  printf 'OPENROUTER_API_KEY=%s\n' "$OPENROUTER_KEY" > .env
  unset OPENROUTER_KEY
fi

if [ -f /root/null-run.pid ] && kill -0 "$(cat /root/null-run.pid)" 2>/dev/null; then
  echo "A deadline run is already active with PID $(cat /root/null-run.pid)." >&2
  exit 1
fi

nohup env \
  VM_TIME_LIMIT_S=20 \
  VM_BUDGET_USD=1.00 \
  VM_VERIFY_RESERVE_S=1 \
  LEAN_CHECK_TIMEOUT_S=1 \
  COMPARATOR_TIMEOUT_S=1 \
  .venv/bin/python run.py \
    --problems sample-problems \
    --out outputs \
    --n-workers 1 \
  > /root/null-run.log 2>&1 &

RUN_PID=$!
printf '%s\n' "$RUN_PID" > /root/null-run.pid
echo "Deadline run launched with PID $RUN_PID"
echo "Monitor with: tail -f /root/null-run.log"
echo "After it finishes, validate the newest directory under outputs/submission/."
