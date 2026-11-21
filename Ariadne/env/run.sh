#!/bin/sh
# Run a command inside the Ariadne toolchain image, as the calling user,
# with the current directory mounted at /work (the working directory) and
# the whole Ariadne/ directory mounted at /ariadne (for shared files such
# as bench/sglib and plugin/share).
#   usage: Ariadne/env/run.sh <command> [args...]
# Memory limit (2026-11-18): ARIADNE_MEM, default 16g, no extra swap.
set -eu
image="${ARIADNE_IMAGE:-ariadne-m0:dev}"
mem="${ARIADNE_MEM:-16g}"
ariadne="$(cd "$(dirname "$0")/.." && pwd)"
exec docker run --rm -i --init ${ARIADNE_NAME:+--name "$ARIADNE_NAME"} \
  --memory "$mem" --memory-swap "$mem" --pids-limit 1024 \
  --user "$(id -u):$(id -g)" \
  -e HOME=/home/rocq \
  -v "$ariadne:/ariadne" \
  -v "$(pwd):/work" -w /work \
  "$image" bash -lc 'exec "$@"' bash "$@"
