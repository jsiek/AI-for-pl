M5 instantiation inversion blocker: under-lift generated reveals

Date: 2026-08-12

Latest synthesis route tested:

  Do not exchange generated reveal evidence.  Transport only the old body
  derivation into the final under-left fresh world, then generate the two
  target reveals directly there.

Checked progress:

  `InstInversionProof.agda` now contains the old-evidence prefix

    `Λ⊑Λ²-route1ᴸ-prefix`

  with statement shape:

    from

      `liftWorldBoth X⊑X (liftWorldLeft X⊑★ W) ∣ γᴮ ⊢² V ⊑ V′ ∶ body-p`

    produce

      `ΛLiftToBindFreshWorldᴸ X⊑★ W ∣ γᵇ ⊢² V
         ⊑ renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵇ`

    where

      `pᵇ : A ⊑ᵂ⟨ ΛLiftToBindFreshWorldᴸ X⊑★ W ⟩
              renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B`

  The checked composition is:

    1. `TargetExtend.⊢²-target-insert` under
       `liftWorldBoth X⊑X (liftWorldLeft X⊑★ _)` for `bind ★`;
    2. `TermImpDecay.⊢²-decay` under the both-lift, changing the body
       binder mark from `X⊑X` to `X⊑★`;
    3. `CenterRename.⊢²-extend-center` for the fresh abstract target
       center;
    4. `TargetBindLift.⊢²-target-bind-lift-move` with
       `freshLiftToBindTargetMove★ᴸ`.

  Checked command:

    AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp -v0 \
      GTSFImp/proof/DGG/Catchup/InstInversionProof.agda

Where in-place reveal generation blocks:

  The final old-evidence world is:

    `ΛLiftToBindFreshWorldᴸ X⊑★ W`

  whose embeddings are:

    source: `skip (keep (keep (skip (ηᴸʷ W))))`
    target: `skip (keep (skip (keep (ηᴿʷ W))))`

  Therefore:

    current source binder `zero`     maps to center `suc zero`
    outer source binder `suc zero`  maps to center `suc (suc zero)`
    target alias `zero`             maps to center `suc zero`
    target representative `suc zero` maps to center
      `suc (suc (suc zero))`

  The first generated reveal would need a wrapper

    `⊑reveal² mono rb ...`

  with

    `rb : RebaseAtᴿ Wmid (ΛLiftToBindFreshWorldᴸ X⊑★ W) (just zero)`

  so that the premise is the checked old-evidence derivation.  Since
  `RebaseAtᴿ` is defined by `rebase-varᴿ` around a full `RebaseAt`, the
  hidden field

    `RebaseAt.pivotAligned`

  must align some source pivot in the premise world with target variable
  `zero`.  In `ΛLiftToBindFreshWorldᴸ X⊑★ W`, only source variable `zero`
  maps to the alias center `suc zero`; source variable `suc zero` maps to
  `suc (suc zero)`.  Thus the hidden source pivot is forced to be
  `zero`.

  But the generated reveal's target type replaces the alias with the
  representative:

    `replaceTy zero (⇑ᵗ (＇ zero)) (applyBody (bind ★) B)`

  so the conclusion world `Wmid` must support the body relation with the
  current source pivot aligned to target variable `suc zero`, whose center
  is `suc (suc (suc zero))`.  At the same time the hidden

    `RebaseAt.ηᴸ-off-pivot`

  field must keep the older source binder `suc zero` fixed at
  `suc (suc zero)`.

  That asks for an order-preserving source OPE with:

    `toRenameᵗ (ηᴸʷ Wmid) zero ≡ suc (suc (suc zero))`
    `toRenameᵗ (ηᴸʷ Wmid) (suc zero) ≡ suc (suc zero)`

  No `_↪ᵗ_` can witness this same-side source reversal.  The target store
  typing is not the obstruction; the exact anchoring fields are
  `RebaseAt.pivotAligned` and `RebaseAt.ηᴸ-off-pivot`.

Consequence:

  `RebaseAtᴿ` is syntactically indexed by a target variable, but generated
  target reveals are not independent of center order: their hidden
  `RebaseAt` re-parks a source pivot.  Under an existing source lift, the
  first generated reveal would have to move the current source binder past
  the older source binder.  That is the same-side exchange that this arc
  already established is unsound.

  The old-evidence fused prefix is complete and checked, but the in-place
  under-lift reveal generation does not close.  Therefore the recursive
  `Λ⊑²` case, the source-strip cases, and `Λ-package` remain unclosed in
  this branch.

No live relation was changed, and no postulate, hole, catch-all, or live
statement weakening was added.

RESOLVED (2026-08-12, live witness commit `da0541e`):

  The in-place generated-reveal route remains blocked for the current
  front-lift world order described above.  M-3 resolves the satisfiability
  issue by using the A3 smart-comma premise layout rather than by generating
  those reveals in the old under-lift world.  The checked live witness is
  `proof.DGG.SmartCommaWitness.d1-top-smart-live`; it derives the same D1
  post-reduction relation at the two-allocation world through the live
  `Λ⊑²-smart-comma` constructor.
