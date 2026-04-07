# `SystemF/lean/extrinsic` Design Note

This Lean development tracks the Agda `SystemF/extrinsic` structure
including the deliberate design choice: type-into-term transport is
identity-on-terms.

- Lean names (in `Terms.lean`): `renameTT`, `substTT`, `substOneTT`
- Agda names (in `Terms.agda`): `renameᵀ`, `substᵀ`, `_[_]ᵀ`

So while the names differ slightly between Lean and Agda, the intended behavior
is the same in this port: these operations do not recursively traverse term
syntax.

This choice simplifies parts of the metatheory, especially the relational
parametricity development and the fundamental theorem.
