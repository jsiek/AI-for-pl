#!/bin/sh
# Which lemma slows SMT down on sglib_dllist_add's goals?  For each lemma
# named on the command line, remove it from a scratch copy of b1.c and run
# WP on add's non-RTE goals.  (Diagnostic; not part of check.sh.)
#   usage: ./lemma_ablation.sh dll_links dll_first ...
set -u
for lemma in "$@"; do
  python3 -I - "$lemma" <<'EOF'
import re, sys
name = sys.argv[1]
s = open("b1.c").read()
i = s.index(f"    lemma {name}")
# up to the next top-level spec item (lemma, predicate, comment, end)
m = re.compile(r"\n    (lemma|predicate|inductive|//)|\n\*/").search(s, i + 1)
j = m.start() + 1
open("ablate_tmp.c", "w").write(s[:i] + s[j:])
EOF
  printf '%s removed: ' "$lemma"
  ../../env/run.sh frama-c \
    -load-module /ariadne/plugin/_build/default/ariadne.cmxs \
    -cpp-extra-args="-I/ariadne/plugin/share" \
    -generated-spec-custom terminates:skip -ariadne ablate_tmp.c \
    -then -wp -wp-rte -wp-model Typed -wp-fct sglib_dllist_add \
    -wp-prop=-rte,-ariadne -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
    -wp-cache none -wp-session /work/session_ablate > ablate.log 2>&1; grep -E "Proved goals|rror" ablate.log \
    | tr -s " "
  rm -rf ablate_tmp.c session_ablate
done
