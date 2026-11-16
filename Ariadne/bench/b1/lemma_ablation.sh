#!/bin/sh
# Which lemma slows SMT down on sglib_dllist_add's goals?  For each lemma
# named on the command line, remove it from a scratch copy of b1.c (with
# the spec templates expanded) and run WP on add's non-RTE goals.
# (Diagnostic; not part of check.sh.)
#   usage: ./lemma_ablation.sh dll_links dll_first ...
set -u
python3 -I ../../harness/acsl_expand.py b1.c ablate_src.c \
  --cpp-args="-I/ariadne/plugin/share -I/ariadne/bench/sglib_spec" || exit 1
for lemma in "$@"; do
  python3 -I - "$lemma" <<'EOF'
import re, sys
name = sys.argv[1]
s = open("ablate_src.c").read()
i = s.index(f" lemma {name}")
# up to the next spec item (lemma, predicate, inductive) or the end
m = re.compile(r" (lemma|predicate|inductive)\b|\s*\*/").search(s, i + 1)
j = m.start()
open("ablate_tmp.c", "w").write(s[:i] + s[j:])
EOF
  printf '%s removed: ' "$lemma"
  ../../env/run.sh frama-c \
    -load-module /ariadne/plugin/_build/default/ariadne.cmxs \
    -cpp-extra-args="-I/ariadne/plugin/share -I/ariadne/bench/sglib_spec" \
    -generated-spec-custom terminates:skip -ariadne ablate_tmp.c \
    -then -wp -wp-rte -wp-model Typed -wp-fct sglib_dllist_add \
    -wp-prop=-rte,-ariadne -wp-prover alt-ergo,z3,cvc5 -wp-timeout 60 \
    -wp-cache none -wp-session /work/session_ablate > ablate.log 2>&1; grep -E "Proved goals|rror" ablate.log \
    | tr -s " "
  rm -rf ablate_tmp.c session_ablate
done
rm -f ablate_src.c
