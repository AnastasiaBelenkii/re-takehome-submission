#!/usr/bin/env bash
# One-time applicant setup. Lean itself is only pulled as a prebuilt image.
set -euo pipefail
cd "$(dirname "$0")/.."

PYTHON_BIN=${PYTHON_BIN:-}
if [[ -z "$PYTHON_BIN" ]]; then
  for candidate in python3.13 python3.12 python3.11 python3; do
    if command -v "$candidate" >/dev/null 2>&1 && "$candidate" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))'; then
      PYTHON_BIN=$(command -v "$candidate")
      break
    fi
  done
fi
[[ -n "$PYTHON_BIN" ]] || { echo "Python 3.11+ is required." >&2; exit 1; }
"$PYTHON_BIN" - <<'PY'
import sys
if sys.version_info < (3, 11):
    raise SystemExit("PYTHON_BIN must select Python 3.11+")
PY
command -v docker >/dev/null 2>&1 || { echo "Docker is required." >&2; exit 1; }
docker version >/dev/null 2>&1 || { echo "Docker is installed but its daemon is not running." >&2; exit 1; }

if [ ! -d .venv ]; then
  "$PYTHON_BIN" -m venv .venv
fi
.venv/bin/python -m pip install --quiet --upgrade pip
.venv/bin/python -m pip install --quiet -e .

IMAGE=$(.venv/bin/python - <<'PY'
from re_harness.config import HarnessSettings
print(HarnessSettings.from_env(n_workers=1).lean_image)
PY
)
echo "Pulling the complete Lean/Mathlib runtime: $IMAGE"
docker pull "$IMAGE"
docker run --rm --network=none --read-only --user 65532:65532 \
  --cap-drop=ALL --security-opt no-new-privileges=true \
  --tmpfs /tmp:rw,nosuid,nodev,size=64m,mode=1777 \
  --tmpfs /work:rw,nosuid,nodev,size=64m,mode=1777 \
  "$IMAGE" health

if [ ! -f .env ]; then
  echo
  echo "Next: cp .env.example .env and add the OpenRouter key from your email."
fi
echo "Setup complete. Lean and Mathlib are entirely inside the Docker image."
