* DONE: Move strong-rep-var/TypeSubst.agda to strong-rep-var/proof/

* DONE: Merge the examples in notes/RepresentationReductionExamples.agda
  into the file strong-rep-var/Examples.agda

* Port the COLOR PRESERVATION theorem to strong-rep-var.

  The original is on branch strong-v3-design, proved 2026-09-12
  (commit 31fa0918, "proof of color preservation") and retired
  2026-09-15 by the v8 sweep (309ad95a); it was never on main.  The
  last fully-alive version is commit db3d7fb8:

    git show db3d7fb8:SystemF/agda/strong/ColorPreservation.agda
    git show db3d7fb8:SystemF/agda/strong/proof/ColorPreservation.agda
    git show db3d7fb8:SystemF/agda/strong/Residual.agda

  The v7 statement: for a well-typed plug C M reducing to plug D N with
  N the residual of M along the run, the two holes' contexts have equal
  lexical type-variable scope (scopeᵗ Δ₁ ≡ scopeᵗ Δ₂) — "a non-boundary
  term's color never changes during reduction" (design law, commit
  5214b055).  The proof factors through a push/pop balance for one-hole
  contexts.

  Porting notes: the v7 vocabulary (merged entries, computed contexts)
  is gone here, so this is a restatement, not a transcription.  "Color"
  becomes the SCOPE MAP around a residual position (which ordinary
  names are live, and which α each denotes).  The engine should be the
  fact proof/ShiftAudit.agda already records — every move except
  TyBeta's is representation-only, so ordinary scope never moves — plus
  a Residual/one-hole-context layer that does not exist in this tree
  yet and must be rebuilt.  Per the standing protocol, the STATEMENT
  goes to Jeremy for review before the proof is attempted.
