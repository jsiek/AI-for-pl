# `SystemF/agda/curry` design note

This development intentionally omits the usual structural action of
type renaming/substitution on terms: the corresponding operations are
not defined in `Terms.agda` because they would be identities.

This is a deliberate deviation from the common System F setup. The
goal is to simplify parts of the metatheory, especially relational
parametricity proofs, including the fundamental theorem.
