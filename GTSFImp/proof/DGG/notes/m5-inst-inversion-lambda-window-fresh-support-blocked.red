M5 instantiation inversion blocker: window-fresh support still needs image data

Date: 2026-08-12

Checked progress in the live proof:

  `Catchup/InstInversionProof.agda` now contains the window-fresh
  invariant layer:

    `liftTargetWindow`
    `TargetPivotFresh`
    `RebaseAtWindowFresh`
    `RebaseAtᴿWindowFresh`
    `RebaseAtᴸWindowFresh`
    `TagRebaseAtᴸWindowFresh`
    `WindowFresh²`

  It also contains the freshness-aware derivation transport surface:

    `CenterMapWindowSupport`
    `⊢²-center-map-window`

  The induction covers every `CastTermImprecision2` constructor.  The
  wrapper cases consume the actual wrapper's freshness proof and recurse
  with the returned premise map/support.

  Finally, TargetExtend image discharge is checked:

    `⊢²-target-insert-window-fresh`

  Statement shape:

    if `ins : TargetInsert ρ π W W⁺` and every old target image
    `toRenameᵗ ρ X` is off the exchange window, then the derivation
    produced by `⊢²-target-insert ins rel` is `WindowFresh²` for that
    window.

Checked commands:

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    GTSFImp/proof/DGG/Catchup/InstInversionProof.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    GTSFImp/All.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    M5InstInversionDesignScratch.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
    M5RelContinuationScratch.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
    -i GTSFImp/proof/DGG/notes -v0 \
    GTSFImp/proof/DGG/notes/SideStableCycleCounterScratch.agda

Exact field that still blocks:

  The first concrete support closure obligation is still the source-repark
  forward field, now freshness-indexed:

    `rebaseAtForwardFresh :
       (rb : RebaseAt W Wᵖ Xᴸ Xᴿ) →
       RebaseAtWindowFresh Window rb →
       ImpEnvMono W Wᵖ →
       Σ Wᵖˣ. Σ ρᵖ. Σ mpᵖ.
         CenterMapWindowSupport Window mpᵖ
         × ImpEnvMono Wˣ Wᵖˣ
         × RebaseAt Wˣ Wᵖˣ Xᴸ Xᴿ`

  The no-on-window fact rules out the checked counterexample where the
  source re-park lands directly on the generated target center.  However,
  by itself it does not provide the positive image/reachability witness
  needed to construct the cycle-corrected premise map:

    1. which old target center the pivot re-parks onto,
    2. how that old center is represented through the current premise map,
    3. the induced total center function `ρᵖ`,
    4. `impEnv-map` / `impEnv-unmap` for the cycle image, and
    5. recursive `CenterMapWindowSupport Window mpᵖ`.

  The checked TargetExtend discharge proves the inserted derivation is
  window-fresh, but that boolean freshness proof forgets the old-center
  witness supplied by `target-center-reflect`.  The support field above
  receives only `RebaseAtWindowFresh Window rb`, so the cycle combinator
  cannot recover the TargetInsert image data it needs.

Consequence:

  The invariant and insertion discharge are now checked, and the previous
  on-window counterexample is excluded.  The remaining design surface must
  be strengthened from "pivot is not in the fresh window" to a parked-
  reachability/image invariant that carries the reflected old target
  witness through wrapper premise worlds.  Without that witness, the
  concrete `CenterMapWindowSupport` constructors for the top-level and
  under-right exchanges remain underspecified.

No live relation was changed, and no postulate, hole, catch-all, or live
statement weakening was added.
