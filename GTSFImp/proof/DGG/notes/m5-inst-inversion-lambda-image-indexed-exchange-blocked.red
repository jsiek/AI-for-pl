M5 instantiation inversion blocker: image-indexed exchange meets generated reveals

Date: 2026-08-12

Approved route tested:

  Fuse the cross-side exchange with the two-bind target insertion, so the
  arbitrary body derivation is transported from its original pre-insertion
  form together with the TargetInsert image data.  This removes the
  forgotten-witness problem from the previous window-fresh support layer:
  old rebase evidence has its old target pivot, its inserted image, and the
  target-center-reflect freshness facts available during the induction.

Checked progress before this blocker:

  `TargetBindLift.agda` now has the under-left fresh target-store move:

    `ΛLiftToBindFreshWorldᴸ`
    `freshLiftToBindMoveᴸ`
    `freshLiftToBindTargetMove★ᴸ`

  Checked command:

    AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
      GTSFImp/proof/DGG/TargetBindLift.agda

  This confirms that, after inserting the first fresh target bind under an
  existing left lift and decaying X⊑X to X⊑★, the lift-to-bind step is still
  target-store bookkeeping rather than substitution-shaped.

Where the fused route blocks:

  There are two possible places to apply the fused exchange, and both expose
  a different obstruction.

  1. Exchange before rebuilding the generated target reveals.

     The pre-reveal exchanged fresh world for one outer source-only lift is:

       `ΛLiftToBindFreshWorldᴸ X⊑★ W`

     Its source/target center order is:

       current source, current target alias, outer source, target rep

     The inner generated reveal has target type:

       `replaceTy zero (⇑ᵗ (＇ zero)) (applyBody (bind ★) B)`

     so the source occurrence at `zero` in `A` must be transported to the
     target occurrence at `suc zero` (the representation target).  In this
     exchanged order, that target representation center is behind the older
     source-only binder.  The reveal premise would therefore need a source
     OPE whose newer source variable maps after the older source variable.
     That is a same-side order reversal, hence no `_↪ᵗ_` can witness it.

     Equivalently, the generated inner reveal can be rebuilt in the born
     order:

       current source, current target alias, target rep, outer source

     but not in the exchanged order:

       current source, current target alias, outer source, target rep

     because the intermediate relation after the inner reveal aligns the
     current source with the target rep.

  2. Exchange after the closed depth-0 base transport at the lifted base.

     This keeps the generated reveals sound internally, but the derivation
     being exchanged is no longer merely a TargetExtend image of the
     original body derivation.  It contains the two generated `⊑reveal²`
     wrappers, whose rebases are deliberately on the fresh target window.
     The image-indexed induction over old evidence does not apply to those
     wrappers.  Extending the exchange to cover them reintroduces the same
     non-OPE premise shape described above.

Why this is not the previous counterexample:

  The permanent finite counterexample in
  `m5-inst-inversion-lambda-side-stable-cycle-output-blocked.red` still does
  not instantiate the image-indexed theorem for the original body derivation:
  it is an arbitrary post-insertion source re-park onto a fresh window center
  and lacks the pre-insertion TargetInsert image witness.  The new obstruction
  is different: the Λ post step itself creates on-window generated reveal
  rebases, and those wrappers are necessary to type the reduct.

Consequence:

  The fused theorem is plausible for the old body relation and should reduce
  its old rebase cases to the proven TargetExtend commutes.  It is not enough
  to close the `Λ⊑²` recursive case, because the consumer also needs the two
  generated target reveals.  A successful design must either keep the reveal
  premises in born order while presenting a `CTI2.Λ⊑²`-compatible outer
  package, or change the recursive package/tower orientation so the generated
  reveal intermediates are not forced through the exchanged order.

No live relation was changed, and no postulate, hole, catch-all, or live
statement weakening was added.
