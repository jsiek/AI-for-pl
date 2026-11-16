#!/bin/sh
# Run a command inside the Ariadne toolchain image, as the calling user,
# with the current directory mounted at /work (the working directory) and
# the whole Ariadne/ directory mounted at /ariadne (for shared files such
# as bench/sglib and plugin/share).
#   usage: Ariadne/env/run.sh <command> [args...]
set -eu
image="${ARIADNE_IMAGE:-ariadne-m0:dev}"
ariadne="$(cd "$(dirname "$0")/.." && pwd)"
exec docker run --rm -i --init ${ARIADNE_NAME:+--name "$ARIADNE_NAME"} \
  --user "$(id -u):$(id -g)" \
  -e HOME=/home/rocq \
  -v "$ariadne:/ariadne" \
  -v "$(pwd):/work" -w /work \
  "$image" bash -lc 'exec "$@"' bash "$@"
