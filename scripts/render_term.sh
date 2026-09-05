#!/bin/bash
# Render a strong-System-F de Bruijn term/type/boundary to NAMED notation.
# Uses strong/Show.agda via the type-error trick: `oops : e ≡ ""` makes
# Agda print e's normal form in the mismatch error.
#   usage: scripts/render_term.sh '<String expr>' ['<import line>' ...]
#   example: scripts/render_term.sh 'showTmIn 1 T₆' \
#              'open import strong.Examples'
set -u
cd "$(dirname "$0")/../SystemF/agda" || exit 1
EXPR="$1"; shift
{ echo "module RenderTmp where"
  echo "open import Relation.Binary.PropositionalEquality using (_≡_)"
  echo "open import Data.String using (String)"
  echo "open import strong.Show"
  for imp in "$@"; do echo "$imp"; done
  echo "oops : ($EXPR) ≡ \"\""
  echo "oops = _≡_.refl"
} > RenderTmp.agda
OUT=$(agda -v0 RenderTmp.agda 2>&1)
rm -f RenderTmp.agda RenderTmp.agdai _build/*/agda/RenderTmp.agdai 2>/dev/null
# the normal form is everything before the != in the mismatch error
echo "$OUT" | tr '\n' ' ' | sed -e 's/.*error: \[UnequalTerms\] *//' \
  -e 's/ *!=.*//' -e 's/^"//' -e 's/"$//'
echo
