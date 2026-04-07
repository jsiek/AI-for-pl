# System F (Lean)

This directory contains the Lean port/build setup for the System F development.

The default `lake` build now includes:
- the full `curry/*` development
- intrinsic core modules via `intrinsic/Intrinsic.lean`
- intrinsic logical-relations scaffold via `intrinsic/LogicalRelation.lean`

There is also an intrinsic-only core target:
- `lake build intrinsic`

There is also a curry-only target:
- `lake build curry`

`intrinsic/LogicalRelation.lean`, `intrinsic/Parametricity.lean`, and
`intrinsic/FreeTheorems.lean` are still under active porting and are
not yet added as default build roots.

## Note on `ProductOmega`

There is intentionally no `ProductOmega` module in this Lean
directory.  In the Agda development, `ProductOmega` is used as a
workaround related to predicativity constraints. Lean is impredicative
(`Prop`), so that extra module is not needed here.
