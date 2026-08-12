M5 instantiation inversion blocker: cross-side premise OPE reification

Date: 2026-08-12

Blocked target:

  the approved derivation-level cross-side center exchange needed after
  applying the closed depth-0 `Λ⊑Λ²-post-body-transport` at the lifted
  base world.

Statement form tried:

  minimal adjacent exchanges, composed twice:

    1. under the outer generated right bind:

       rightOnlyWorld
         (rightOnlyWorld (liftWorldLeft X⊑★ W) B₁) B₂

       to

       rightOnlyWorld
         (liftWorldLeft X⊑★ (rightOnlyWorld W B₁)) B₂

    2. top-level:

       rightOnlyWorld (liftWorldLeft X⊑★ W) B

       to

       liftWorldLeft X⊑★ (rightOnlyWorld W B)

  The existing one-bind obligation lemma
  `right-left-exchange-⊑ᵂ` proves the type-imprecision leg for step 2 by
  `rename-⊑ swap01 ...`; the under-right step is the same swap lifted
  under one generated right center.

Validated reuse:

  The imprecision layer already supports the required arbitrary
  injective center map through `rename-⊑`, and the side-stable argument
  is enough for ordinary obligation fields: both source and target
  embeddings are composed with the same injective swap, so
  `CenterAligned`-style equalities are preserved.

New resister:

  A derivation-level induction must replay through all wrapper
  constructors.  For each wrapper constructor the recursive premise is
  not just an obligation in the conclusion world; it lives in a premise
  world supplied by rebasing evidence:

    `⊑reveal²`              field: `RebaseAtᴿ W W′ Xᴿ?`
    `⊑conceal²`             field: `RebaseAtᴿ W′ W Xᴿ?`
    `reveal⊑²`              field: `RebaseAtᴸ W W′ Xᴸ?`
    `conceal⊑²`             field: `TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?`
    `reveal⊑reveal²`        field: `RebaseAt W Wᵖ Xᴸ Xᴿ`
    `conceal⊑conceal²`      field: `RebaseAt Wᵖ W Xᴸ Xᴿ`
    `packaged-seal-star²`   field: `RebaseAt Wᵖ W Xᴸ Xᴿ`

  `TargetExtend` handles the analogous problem for target insertions by
  constructing `insertRebaseWorld ins Wᵖ`.  That construction depends on
  the center map being an OPE (`π : Δ ↪ᵗ Δ′`), so the new source and
  target embeddings are available as OPEs by composition.

  The adjacent cross-side swap is not an OPE.  Even though it is
  side-stable for this exchange, the `World` record stores embeddings as
  OPEs, not arbitrary injective maps.  The proof therefore needs a new
  OPE reification lemma:

    if an adjacent swap is order-preserving on the source image and on
    the target image separately, construct the swapped source and target
    embeddings as `_↪ᵗ_` values, with equalities showing their
    `toRenameᵗ` functions are the swapped embeddings.

  Without that OPE reification, the wrapper constructors have no
  well-typed exchanged premise world to recurse into.  The first failing
  constructor in a CenterRename-style induction would be `⊑reveal²`,
  at its `RebaseAtᴿ W W′ Xᴿ?` field: the output constructor needs an
  exchanged `W′` plus `RebaseAtᴿ Wˣ W′ˣ Xᴿ?`, but the available facts
  only prove equality after applying the swap function, not the required
  `ηᴸʷ`/`ηᴿʷ` OPE fields of `W′ˣ`.

Consequence:

  The type-obligation exchange remains sound and checked.  The
  derivation theorem needs an additional low-level side-stable OPE
  reification surface before the constructor induction can be completed
  without postulates or weakening CTI2.

No live relation was changed, and no postulate, hole, or catch-all was
added.

Postscript 2026-08-12:

  The requested OPE foundation is now checked in
  `Catchup/InstInversionProof.agda`: `Swap01OPE`, `AdjacentSwapOPE`,
  `swapWorld`, `CenterMapWorld`, and the generated target-side
  `RebaseAtᴿ` commutes for both the top-level and under-right exchange
  positions.

  The remaining blocker has moved from OPE reification itself to the
  recursive support surface for the full derivation-level exchange; see
  `m5-inst-inversion-lambda-center-map-support-blocked.red`.
