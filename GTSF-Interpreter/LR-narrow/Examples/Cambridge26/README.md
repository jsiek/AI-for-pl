# Cambridge26 logical-relation specifications

This directory replaces the incomplete encodings in
`GTSF/NarrowingExamples.agda` for purposes of `LR-narrow`. That older module
uses the obsolete `TermNarrowing` relation, covers only an earlier subset of
the examples, permits unsolved metavariables, and is therefore not evidence
that the Cambridge26 claims fit the current logical relation.

Each numbered module defines a closed, type-checked `ClosedExample` containing
the two endpoint terms, both endpoint typing derivations, and the exact live
type-imprecision derivation `p`. Its syntax uses the source-to-target
orientation

`precise-term ⊑ imprecise-term`,

which is the reverse of the Cambridge note's displayed `⊒` orientation. The
LR's semantic arguments and the `ClosedExample` record follow the display:
imprecise-left, precise-right. For every such record `example`, the intended
semantic claim is exactly `Membership example`, i.e.
`TermRelation p I k [] [] imprecise-term precise-term` for every initial
interpretation and logical index. These files specify those proof obligations;
most do not claim that the still-incomplete fundamental theorem has discharged
them. `Example05.example-membership` is the first direct exception: it proves
its closed obligation from the two concrete interpreter computations.

`LabeledPrograms.agda` checks programs (a)--(d), and
`LabeledRelations.agda` checks relations (e)--(g). `All.agda` is the aggregate
regression module. `Renderings.agda` applies `Pretty.TypedTerms` to both
endpoint typing derivations and `Pretty.Narrowings` to an actual checked
narrowing derivation. Thus each generated `A ⊒ B : c` obtains `A`, `B`, and
`c` from one proof object. `Rendition.lagda.md` is the corresponding literate
catalogue; it also records the post-reduction terms shown in the original
notes, without importing reduction into the LR development.

`K/` adds 20 analogous specifications for the polymorphic K combinator. They
cover the precision square obtained by making K's result-producing `X` binder
and discarded-argument `Y` binder dynamic independently, both orders of
reaching the fully dynamic vertex, applications, both complete round trips,
and direct generalization of raw dynamic K to the polymorphic type.
`K/All.agda` is their aggregate checker; `K/Renderings.agda` is the matching
list of typed endpoints, checked narrowing judgments, and LR obligations.

## Corrections and canonicalizations

- Labeled example (g) is ill-typed as printed. Its final instantiation cast
  produces `★ ⇒ ★`, whereas the note annotates the term with a universal
  type. `example-g-corrected` records the dynamic endpoint.
- Example 3 is shown at an open, allocated intermediate state. Its encoding
  closes that state with the compiled `ν α := Nat` type application.
- Examples 5 and 6 assume constants at two distinct base types. The repository
  has natural-number constants only. Their checked encodings use a tagged
  function value, whose ground tag `★ ⇒ ★` differs from `Nat`, preserving the
  intended tag-mismatch behavior without inventing an untyped constant.
- Example 17's heading omits the second application although its subsequent
  trace uses it. The encoding applies both `42` and `69` so the endpoint is a
  base result rather than a function.
- Example 22 contains type-imprecision claims only, so it is represented by
  two `TypeExample` values rather than fabricated terms.

## `split` and `extend`

No `split` or `extend` constructor is copied into the LR.

The uses of `split` distinguish physical seals produced by separate
allocations. In `LR-narrow`, that information belongs to the Kripke `World`:
paired binder extensions allocate two fresh seals and record their pairing.
The type-imprecision proof remains unchanged.

The uses of `extend` strengthen an already allocated interpretation without
changing either endpoint term. This should become an admissible
future-interpretation/world-extension lemma, not a new clause of
`ValueNarrowing`. The closed specifications deliberately stop before choosing
a particular intermediate allocation schedule; their eventual proofs may move
to suitable future worlds as evaluation exposes the seals.

This division is testable: all endpoint programs and type-imprecision indices
in this directory type-check without either rule and without importing
small-step reduction.
