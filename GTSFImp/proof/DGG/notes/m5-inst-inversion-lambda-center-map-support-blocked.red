M5 instantiation inversion blocker: recursive center-map support surface

Date: 2026-08-12

Completed before this blocker:

  The side-stable OPE foundation requested after
  `m5-inst-inversion-lambda-cross-side-premise-ope-blocked.red` is now live
  and checked in `Catchup/InstInversionProof.agda`:

    `Swap01OPE`
    `NoKeepKeep01`
    `swap01-reify-ope`
    `AdjacentSwapOPE`
    `adjacent-swap-ope-rename`

  The indexed adjacent relation is closed under `skip` and `keep`, so the
  top-level swap and the under-outer-right swap are instances of the same
  reification surface.

  The swapped-world layer is also checked:

    `CenterMapWorld`
    `swapWorld`
    `swapWorld-map`
    `center-map-⊑ᵂ`
    `center-map-ctx`
    `center-map-same-ctx`
    `center-map-imp-mono`
    `center-map-lift-both`
    `center-map-lift-left`
    `center-map-store-rep`
    `center-map-rebase-at`
    partner predicate transports

  Concrete generated-target commutes are checked for the two exchange
  positions:

    `right-left-center-map`
    `right-left-rebase-atᴿ`
    `right-left-under-right-center-map`
    `right-left-under-right-rebase-atᴿ`

  These discharge the first `⊑reveal²`-style premise-world OPE problem for
  the generated top-level and under-right target reveal positions.

Checked commands:

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    GTSFImp/proof/DGG/Catchup/InstInversionProof.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    GTSFImp/All.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    M5InstInversionDesignScratch.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    M5RelContinuationScratch.agda

New resister:

  The derivation-level exchange cannot be stated from `CenterMapWorld`
  alone.  Wrapper constructors need the exchanged recursive premise world,
  its own center-map evidence, and the rebuilt wrapper evidence.  For the
  induction to recurse, that premise map must also carry the same support.

  The next sound theorem surface therefore needs an explicit recursive
  support package, for example:

    `CenterMapSupport mp`

  with Σ-producing fields shaped like:

    `RebaseAtᴿ W Wᵖ Xᴿ?`
      ↦ `Σ Wᵖˣ. CenterMapWorld ρ Wᵖ Wᵖˣ × ...`

  and similarly for the reverse/right-conceal, source rebase, tag rebase,
  matched reveal/conceal, packaged seal, and binder-lift cases.

  The first generated target-reveal fields are already proven by
  `right-left-rebase-atᴿ` and `right-left-under-right-rebase-atᴿ`, but the
  full induction also needs the reverse and source-side wrapper directions:

    `⊑conceal²`             needs `RebaseAtᴿ Wᵖ W Xᴿ?`
    `reveal⊑²`              needs `RebaseAtᴸ W Wᵖ Xᴸ?`
    `conceal⊑²`             needs `TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?`
    `reveal⊑reveal²`        needs `RebaseAt W Wᵖ Xᴸ Xᴿ`
    `conceal⊑conceal²`      needs `RebaseAt Wᵖ W Xᴸ Xᴿ`
    `packaged-seal-star²`   needs `RebaseAt Wᵖ W Xᴸ Xᴿ`

  This is not evidence that the exchange is false.  The checked
  `CenterMapWorld` transports show that the fields are insensitive to the
  global source/target interleaving once both side embeddings are reified.
  The unresolved choice is the live theorem surface: a general recursive
  `CenterMapSupport` package versus a narrower generated-target exchange
  specialized to the Lambda post body.

Consequence:

  The type-obligation exchange, OPE reification, generated target-reveal
  premise reification, and binder-lift center maps are checked.  The
  recursive `Λ⊑²` case, source-strip cases, and `Λ-package` assembly remain
  open until the derivation-level support surface is chosen and implemented.

No live relation was changed, and no postulate, hole, or catch-all was added.
