# `SystemF/extrinsic` design note

This development intentionally omits the usual structural action of
type renaming/substitution on terms: `renameᵀ` and `substᵀ` are
identities in `SystemF.agda`.

This is a deliberate deviation from the common System F setup. The
goal is to simplify parts of the metatheory, especially relational
parametricity proofs, including the fundamental theorem.
