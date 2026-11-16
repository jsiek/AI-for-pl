#!/bin/sh
# Rocq 9.0 has `rocq c -config` but not `rocq --config`, which dune's
# `(using rocq 0.11)` mode calls to find installed theories.  The
# Dockerfile puts this script first in PATH, named `rocq`, only while
# building Trakt; every other call goes to the real rocq.
real="$OPAM_SWITCH_PREFIX/bin/rocq"
if [ "$#" -eq 1 ] && [ "$1" = "--config" ]; then
  exec "$real" c -config
fi
exec "$real" "$@"
