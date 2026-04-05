# System F (Lean)

This directory contains the Lean port/build setup for the System F development.

## Note on `ProductOmega`

There is intentionally no `extrinsic/ProductOmega.lean` module in this Lean directory.

In the Agda development, `ProductOmega` is used as a workaround related to predicativity constraints. Lean is impredicative (`Prop`), so that extra module is not needed here.
