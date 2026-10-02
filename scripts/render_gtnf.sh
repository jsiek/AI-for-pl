#!/bin/bash
# Render a GTNF de Bruijn term/type/coercion/run to NAMED notation.
# Uses GTNF/agda/examples/Show.agda via the type-error trick: `oops : e ≡ ""` makes
# Agda print e's normal form in the mismatch error.
#   usage: scripts/render_gtnf.sh '<String expr>' ['<import line>' ...]
#   example: scripts/render_gtnf.sh 'showRun 16 ex1-⊢' \
#              'open import examples.Examples'
#   (`showRun k ⊢M` renders every state of a run with its rules;
#    `showTm M` renders one closed term.)
set -u
cd "$(dirname "$0")/../GTNF/agda" || exit 1
EXPR="$1"; shift
{ echo "module RenderTmp where"
  echo "open import Relation.Binary.PropositionalEquality using (_≡_)"
  echo "open import Data.String using (String)"
  echo "open import examples.Show"
  for imp in "$@"; do echo "$imp"; done
  echo "oops : ($EXPR) ≡ \"\""
  echo "oops = _≡_.refl"
} > RenderTmp.agda
OUT=$(agda -v0 RenderTmp.agda 2>&1)
rm -f RenderTmp.agda RenderTmp.agdai _build/*/agda/RenderTmp.agdai 2>/dev/null
# the normal form is everything before the != in the mismatch error;
# the string's escaped newlines are expanded
echo "$OUT" | tr '\n' ' ' | sed -e 's/.*error: \[UnequalTerms\] *//' \
  -e 's/ *!=.*//' -e 's/^"//' -e 's/"$//' -e 's/\\n/\n/g'
echo
