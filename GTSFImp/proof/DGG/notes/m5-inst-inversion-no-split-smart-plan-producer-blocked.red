M5 instantiation inversion blocker: no-split smart post-plan producer

Status: BLOCKED AT THE RECURSIVE CALLER, 2026-08-13.

Resolved relation question:

  No new `_⊢²_⊑_∶_` constructor is needed for the concrete source-left
  shape.  The live theorem:

    `Λ⊑²-plain-shared-prefix-at`

  derives `ΛPostPrefixPackageAt` for an actual plain `Λ⊑²` over an ordinary
  shared `Λ⊑Λ²`.  It recursively closes the shared inner prefix and rebuilds
  the outer source wrapper with the existing `Λ⊑²-smart-comma` rule.

  The generic consumer also checks:

    `Λ⊑²-plain-shared-prefix-at-base`

Exact remaining caller obligation:

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

Why the first producer attempt is insufficient:

  `TargetExtend.smartFreshGuardInsert` proves that a front smart guard remains
  valid after one or two target insertions.  The checked scratch lemmas are:

    `front-smart-after-target-insert`
    `front-smart-after-two-target-inserts`

  This closure keeps the world chosen by the target-insert pushout.  It does
  not identify that world with the target-window-first smart world used by the
  concrete interleaving.  The attempted equality between those worlds is
  rejected definitionally, so this is not yet the producer required by the
  recursive caller.

Smallest next step:

  State the recursive caller's no-split post plan as explicit quantified
  fields (not a new alias for a theorem conclusion), then construct it either:

    * directly, choosing the two target inserts before rebuilding the pending
      source smart lift; or
    * by a proof-surface bridge from the target-insert pushout world to the
      existing target-window-first smart world.

  Retry the direct rule interleavings before proposing any live relation
  change.  The old S1 split plan may be resumed only if this producer attempt
  ends in a machine-checked obstruction that also excludes the already checked
  concrete derivation tree.

Checked state before stopping:

  Commit `98d3523c` contains the live no-split theorems.  Both the focused
  `InstInversionProof.agda` gate and `GTSFImp/All.agda` pass.  On this computer
  use the Mac-local gate documented in PLAN.md; the old
  `/tmp/agda-work/agda-home` path came from a different machine.

  No live relation was changed, and no postulate, hole, or catch-all was
  added.
