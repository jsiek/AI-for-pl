#!/bin/sh
# Run a command inside the Ariadne toolchain image, with the current
# directory mounted at /work and owned by the calling user.
#   usage: Ariadne/env/run.sh <command> [args...]
set -eu
image="${ARIADNE_IMAGE:-ariadne-m0:dev}"
exec docker run --rm -i \
  --user "$(id -u):$(id -g)" \
  -e HOME=/home/rocq \
  -v "$(pwd):/work" -w /work \
  "$image" bash -lc 'exec "$@"' bash "$@"
