#!/bin/sh
# Why3 1.8.2's prover detection only recognises Coq's old version banner
# ("The Coq Proof Assistant, version ...") and versions up to 8.20.  Rocq
# 9.0 prints "The Rocq Prover, version 9.0.1".  The opam package why3-coq
# 1.8.2 is built against Rocq 9.0, so only the detection rule is stale:
# accept either banner and mark 9.0.x as supported.
#
# Also switch Coq to the coq-ariadne driver (coq.drv + Lia/CoqHammer
# imports), installed next to the standard drivers.
set -eu
d="$(why3 --print-datadir)"
f="$d/provers-detection-data.conf"
cp /tmp/coq-ariadne.drv "$d/drivers/coq-ariadne.drv"
sed -i \
  -e '/^\[ITP coq\]$/,/^$/ s|^driver = "coq"$|driver = "coq-ariadne"|' \
  -e 's|^version_regexp = "The Coq Proof Assistant, version \\\\(\[^ \\n\]+\\\\)"$|version_regexp = "The [A-Za-z ]+, version \\\\([^ \\n]+\\\\)"|' \
  -e '/^\[ITP coq\]$/,/^$/ s|^version_ok = "^8\\.20\\.\[0-9\]+\$"$|version_ok = "^9\\.0\\.[0-9]+$"\n&|' \
  "$f"
grep -A16 '^\[ITP coq\]$' "$f"
