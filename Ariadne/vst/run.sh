#!/bin/sh
# Run a command inside the Ariadne VST image, with the current
# directory mounted at /work and owned by the calling user.
#   usage: Ariadne/vst/run.sh <command> [args...]
# Limits (2026-11-18, after a coqc run exhausted the host's memory):
# ARIADNE_MEM (default 16g, no extra swap) and ARIADNE_TIMEOUT seconds
# per command (default 1800; 0 means none).
set -eu
image="${ARIADNE_VST_IMAGE:-ariadne-vst:dev}"
mem="${ARIADNE_MEM:-16g}"
exec docker run --rm -i --init \
  --memory "$mem" --memory-swap "$mem" --pids-limit 1024 \
  --user "$(id -u):$(id -g)" \
  -e HOME=/home/rocq \
  -v "$(pwd):/work" -w /work \
  "$image" timeout -s KILL "${ARIADNE_TIMEOUT:-1800}" \
  bash -lc 'exec "$@"' bash "$@"
