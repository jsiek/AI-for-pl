# GTSFImp Alternative Semantics — Design Scaffold

This directory hosts an exploration of alternative reduction rules and an
alternative type system for GTSFImp, kept separate from the live
development at [`GTSFImp/`](../). Nothing here is imported by the live
`All.agda`; once a direction stabilizes it will get its own `All.agda`
and `Makefile` following the usual per-directory `make check` shape.

## What the live system commits to

The choices under re-examination, with their rationale entries in
[`Rationale.md`](../Rationale.md):

- **Eager allocation conversion.** Every allocation rule wraps the
  exposed polymorphic body in the recursive upward conversion
  `〖 X ↑ A 〗`, inserting unsealing in positive positions and sealing
  in negative positions ("Allocation reveals the instantiated result").
- **Instantiation closes consistency at `★`.** `β-inst` substitutes `★`
  for the bound variable in the consistency evidence
  (`c [ ★ /0 ]ᶜ`), so the inst-bound variable is mediated entirely by
  `seal`/`unseal` conversions and never survives as a consistency cast
  ("Instantiation closes consistency at star").
- **Binder-directed `gen`/`inst` split.** `gen` fresh variables remain
  as runtime ground *tags* (variable injections are inert values,
  compared by the ordinary tag/untag rules), while `inst` fresh
  variables are eliminated in favor of conversions
  ("Generalization uses fresh-name tags").
- **Typed consistency evidence in the term syntax.** Cast terms carry
  fully typed consistency derivations; the endpoint types live in the
  raw syntax rather than in a separate typing judgment.

These choices are internally coherent, but they are also the source of
most of the administrative-wrapper burden documented in
[`Rationale.md`](../Rationale.md) and carried by the DGG proofs (the
one-sided reveal/conceal rules, pivot-local rebasing, world support,
seal peeling).

## Candidate directions

- **A. Contextual coercions.** Promote the probes in
  [`../experimental/`](../experimental/README.md) to a full alternative
  system: raw coercions (`inst-out X`, `inst-in X`, endpoint-free `id`,
  `inst`, `gen`) typed against a cast context whose entries carry a
  `pending`/`active` allocation phase. `β-inst` then switches the phase
  of the bound variable instead of substituting `★` into the evidence,
  so allocation is a context update rather than a term rewrite.
- **B. Lazy sealing.** Drop the eager `〖 X ↑ A 〗` conversion at
  allocation; seal and unseal on demand when a value actually crosses a
  variable-type boundary. Fewer administrative wrappers in reduced
  terms, at the cost of new canonical-forms analysis at variable type.
- **C. Symmetric `gen`/`inst`.** Remove the binder-directed asymmetry:
  either treat `gen` fresh variables by conversions too (no variable
  ground tags), or treat both by tags. Changes which tag/untag and
  seal/unseal cancellation rules exist and how blame is reported across
  fresh names.
- **D. Grounded-invariant typing.** Fold the store/world invariants
  that the DGG proofs currently reconstruct (mark honesty, alignment,
  canonical store representations) into the type system itself, so they
  are minted by `compile` and preserved by reduction rather than proved
  as companion predicates.

These are starting points, not a menu with a committed winner; the
direction for this branch is an open decision-ask on the PR.
