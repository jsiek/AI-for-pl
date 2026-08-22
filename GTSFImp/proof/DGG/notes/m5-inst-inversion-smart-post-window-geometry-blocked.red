M5 instantiation inversion blocker: smart post-window geometry is not yet
derivable from the M-2 smart target-transport surface

Date: 2026-08-12

Context:

  The post-window geometry surface now exists in the live proof as:

    `ΛPostWindowGeometry W W₂ ext₂`

  and the transport consumer is:

    `Λ⊑Λ²-post-body-transport-at :
       ΛPostWindowGeometry W W₂ ext₂ → ...`

  The concrete right-only instance also checks:

    `Λ-concrete-post-window`

  and the base prefix wrapper now consumes the supplied package:

    `Λ⊑Λ²-base-prefix-at-base :
       ... → ΛPostWindowGeometry W W₂ ext₂ → ...`

  This resolves the concrete lock named in
  `m5-inst-inversion-lambda-base-prefix-at-world-blocked.red`.

New resister:

  The smart recursive prefix needs a geometry instance at the
  pushout-indexed smart premise post world:

    `ΛPostWindowGeometry Wᵐ Wᵐ₂ extᵐ₂`

  where `Wᵐ` is the smart-comma premise world and `Wᵐ₂` is the target-inserted
  smart premise post world produced by the M-2 TargetExtend stack, e.g.

    `smartAliasInsertWorld ins₂ Wᵐ`

  or:

    `smartFreshInsertWorld ins₂ guard`

  The M-2 surface gives the final world and its transported smart guard:

    `smartAliasTargetInsert ins₂ guard`
    `smartFreshTargetInsert ins₂ guard`
    `smartAliasGuardInsert ins₂ guard`
    `smartFreshGuardInsert ins₂ guard`

  plus obligation transport for smart left lifts:

    `SmartCommaLiftᴸ W₂ Wᵐ₂`
    `smartCommaLift-transport⊑ᵂ`

  That is enough to rewrap an outer `Λ⊑²-smart-comma`, but it is not enough
  to build the ordinary `Λ⊑Λ²` post-body transport inside the smart premise.

Missing geometry:

  `ΛPostWindowGeometry` requires two intermediate worlds before the final
  `liftWorldLeft X⊑★ Wᵐ₂`:

  1. `freshWorld`, where the ordinary `Λ⊑Λ²` premise has inserted the first
     generated target bind, decayed `X⊑X` to `X⊑★`, and moved the pending
     source center onto the generated target bind.  In the concrete case this
     is:

       `ΛLiftToBindFreshWorld X⊑★ W`

     and the move is:

       `freshLiftToBindTargetMove★`

  2. `midWorld`, where the inner reveal has reparked that pending source center
     away from the alias/name window.  In the concrete case this is:

       `ΛPostMidWorld W`

  The final smart world from TargetExtend does not include either of these
  intermediate source-center placements, nor a `TargetBindLiftMove` from the
  target-inserted route-one world to the required `freshWorld`.

  Concretely, the unavailable field is not just an obligation transport.  The
  first package field already needs a checked derivation:

    `route1Prefix :
       liftWorldBoth X⊑X Wᵐ ∣ γᴮ ⊢² V ⊑ V′ ∶ body-p
       → Σ[ γᶠ ∈ CtxImp freshWorld ]
         Σ[ pᶠ ∈ A ⊑ᵂ⟨ freshWorld ⟩ applyBody (bind ★) B ]
           freshWorld ∣ γᶠ
             ⊢² V ⊑ renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᶠ`

  Existing `TargetExtend.⊢²-target-insert` can insert targets into an existing
  derivation, and existing `TargetBindLift.freshLiftToBindTargetMove★` can move
  the concrete right-only route-one world.  There is no live theorem composing
  those into a target-inserted smart route-one move.

Smallest next surface:

  Add a smart route-one/post-window support theorem, not a relation rule.  The
  theorem should be statement-first and should produce, from the existing
  target insertion and smart guard:

    * the smart `freshWorld`;
    * the smart `midWorld`;
    * `route1Prefix`;
    * `ImpEnvMono` and `RebaseAtᴿ` for
      `midWorld ← freshWorld` and
      `liftWorldLeft X⊑★ Wᵐ₂ ← midWorld`;
    * context transport / `SameCtx` witnesses;
    * final obligation transport into `liftWorldLeft X⊑★ Wᵐ₂`;
    * target typing context equality.

  Equivalently, generalize `TargetBindLift.freshLiftToBindTargetMove★` to a
  target-inserted smart route-one world and package the two reveal rebases
  around that move.

Checked state:

  The live tree is green after the concrete package checkpoint:

    `AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
       -i GTSFImp/proof/DGG/notes -v0 GTSFImp/All.agda`

    `AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
       -i GTSFImp/proof/DGG/notes -v0 \
       GTSFImp/proof/DGG/notes/M5InstInversionDesignScratch.agda`

  No live relation was changed, and no postulate, hole, or catch-all was added.
