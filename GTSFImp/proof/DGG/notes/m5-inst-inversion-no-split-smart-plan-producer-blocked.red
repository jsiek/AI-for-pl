M5 instantiation inversion blocker: no-split smart post-plan producer

Status: RESOLVED, 2026-08-13.

Resolution:

  `Λ⊑²-plain-shared-smart-plan-prefix-at-base` now checks in
  `Catchup/InstInversionProof.agda`.  It instantiates the generic consumer
  with the existing canonical target-first witnesses:

    `Λ⊑²-smart-fresh-guard`
    `mapCtxᴿ-smart-fresh-liftᴸ`
    `Λ-concrete-post-window`
    `Λ-strip-prefix-p₂`

  The analysis below had the center order after two right bindings
  backwards.  Starting with the front source-fresh guard, the first right
  binding produces `[target₁, sourceFresh, old...]`; the second produces
  `[target₂, target₁, sourceFresh, old...]`.  This is already the
  target-window-first layout required by the generic consumer.  No new
  `TargetInsert` bridge, world equality, or live relation constructor is
  needed.

  The historical blocker analysis is retained below as the rejected route.

Resolved relation question:

  No new `_⊢²_⊑_∶_` constructor is needed for the concrete source-left
  shape.  The live theorem:

    `Λ⊑²-plain-shared-prefix-at`

  derives `ΛPostPrefixPackageAt` for an actual plain `Λ⊑²` over an ordinary
  shared `Λ⊑Λ²`.  It recursively closes the shared inner prefix and rebuilds
  the outer source wrapper with the existing `Λ⊑²-smart-comma` rule.

  The generic consumer also checks:

    `Λ⊑²-plain-shared-prefix-at-base`

Former caller obligation:

  To use the generic theorem below an already smart premise, the recursive
  worker must select a post world `Wᶠ₂` and construct all of:

    `SmartCommaLiftᴸ W₂ Wᶠ₂`

    `SmartLiftCtxᴸ
       (mapCtxᴿ ext₂ γ)
       (mapCtxᴿ extᶠ₂ γᴸ)`

    `ΛPostWindowGeometry
       (liftWorldLeft X⊑★ W) Wᶠ₂ extᶠ₂`

  together with the outer post type obligation.  Once supplied, the generic
  theorem returns the required `ΛPostPrefixPackageAtBase` without changing
  the relation.

Why the first producer diagnosis was incorrect:

  `TargetExtend.smartFreshGuardInsert` proves that a front smart guard remains
  valid after one or two target insertions.  The checked scratch lemmas are:

    `front-smart-after-target-insert`
    `front-smart-after-two-target-inserts`

  This closure keeps the world chosen by the target-insert pushout.  The
  rejected attempt then asked for the wrong world equality because it assumed
  the pending source-fresh center preceded the two target centers.  Computing
  the two insertions shows the opposite order, so the live canonical witnesses
  already discharge the caller obligation without that equality.

Next step after resolution:

  Close the source-strip wrapper cases using the checked specialization,
  assemble `InstInversionPackage.Λ-package`, and wire the dispatcher.  The old
  S1 split plan remains suspended.

Checked state before stopping:

  Commit `98d3523c` contains the live no-split theorems.  Both the focused
  `InstInversionProof.agda` gate and `GTSFImp/All.agda` pass.  On this computer
  use the Mac-local gate documented in PLAN.md; the old
  `/tmp/agda-work/agda-home` path came from a different machine.

  No live relation was changed, and no postulate, hole, or catch-all was
  added.
