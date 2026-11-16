#!/bin/sh
# Run a command inside the Ariadne VST image, with the current
# directory mounted at /work and owned by the calling user.
#   usage: Ariadne/vst/run.sh <command> [args...]
set -eu
image="${ARIADNE_VST_IMAGE:-ariadne-vst:dev}"
exec docker run --rm -i \
  --user "$(id -u):$(id -g)" \
  -e HOME=/home/rocq \
  -v "$(pwd):/work" -w /work \
  "$image" bash -lc 'exec "$@"' bash "$@"
