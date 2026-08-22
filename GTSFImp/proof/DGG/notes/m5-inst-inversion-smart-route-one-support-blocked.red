M5 instantiation inversion blocker: smart route-one support still needs the
parameterized type-obligation transport

Date: 2026-08-12

Context:

  The old window-embedding blocker in
  `m5-inst-inversion-smart-route-one-window-embedding-blocked.red` is resolved
  on the center-geometry side.  The live proof now threads the generated
  target-window embeddings through the route-one construction:

    `ΛRouteOneFreshWorldAt`
    `ΛRouteOneMidWorldAt`
    `ΛRouteOneWindowFacts`
    `Λ-route1-prefix-at`
    `Λ-route1-inner-rebase-at`
    `Λ-route1-outer-rebase-at`
    `Λ-route1-post-window-at`

  The route-one prefix uses the supplied second-window embedding
  `κ₂ : suc Δ₁ ↪ᵗ Δ₂`, which is the place where the smart-fresh pushout must
  pass `EmbeddingPushout.old′ po`.  The middle reveal world also uses the
  first target-window embedding `κ₁ : suc Δ ↪ᵗ Δ₁`, because the source pivot
  must move from target slot `0` to target slot `1` between the two generated
  reveals.

Checked result:

  The following are now live and checked in
  `Catchup/InstInversionProof.agda`:

    * `Λ-route1-prefix-at`:
      transports the ordinary `Λ⊑Λ²` body premise through the first target
      insert, decay, `renameWorld (skip κ₂)`, and
      `freshLiftToBindTargetMoveAtκ`.

    * `Λ-route1-inner-rebase-at`:
      proves the inner reveal pivot rebase from
      `ΛRouteOneMidWorldAt W W₂ κ₁ κ₂` to
      `ΛRouteOneFreshWorldAt W₁ κ₂ (targetStoreʷ W₂)`.

    * `Λ-route1-outer-rebase-at`:
      proves the outer reveal pivot rebase from
      `liftWorldLeft X⊑★ W₂` to `ΛRouteOneMidWorldAt W W₂ κ₁ κ₂`.

    * `Λ-route1-post-window-at`:
      packages those checked center/rebase witnesses into
      `ΛPostWindowGeometry` once the remaining context and type-obligation
      transports are supplied.

New resister:

  Instantiating `ΛPostWindowGeometry Wᵐ Wᵐ₂ extᵐ₂` for the smart premise now
  reduces to constructing:

    `ΛRouteOnePostWindowSupport facts`

  The missing fields are not about `old′` or reveal pivot placement anymore.
  They are the parameterized context and obligation transports:

    `midCtx`
    `outCtx`
    `midFreshMono`
    `outMidMono`
    `outLiftCtxᴸ`
    `innerBody⊑ᵂ`
    `finalBody⊑ᵂ`
    `outTargetCtx`

  The first hard proof obligations are the type-level fields:

    `innerBody⊑ᵂ :
       A ⊑ᵂ⟨ liftWorldBoth X⊑X W ⟩ B
       → A ⊑ᵂ⟨ ΛRouteOneMidWorldAt W W₂ κ₁ κ₂ ⟩
           replaceTy zero (⇑ᵗ (＇ zero)) (applyBody (bind ★) B)`

    `finalBody⊑ᵂ :
       A ⊑ᵂ⟨ liftWorldBoth X⊑X W ⟩ B
       → A ⊑ᵂ⟨ liftWorldLeft X⊑★ W₂ ⟩
           substᵗ Λ⊑Λ²TargetSplit₂ B`

  The existing checked lemmas that provide these for depth 0 are still
  concrete-world lemmas:

    `Λ-inner-body-⊑ᵂ-applyBody`
    `Λ-final-body-⊑ᵂ`

  They hard-code the concrete three-slot substitutions
  `innerρ₃`, `splitSource₃`, and `splitTarget★₃`, and the concrete worlds
  `ΛPostMidWorld W` and
  `liftWorldLeft X⊑★ (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero))`.
  They do not abstract over `κ₁`, `κ₂`, `TargetWindowInsert`, or the
  target-inserted smart pushout world.

Why this is a real interaction boundary:

  The M-2 smart guard transports move obligations from
  `liftWorldLeft X⊑★ W₂` into the final smart premise world, and
  `TargetInsert.transport⊑ᵂ` moves obligations along target insertion.  The
  remaining fields need a different bridge: a parameterized type-substitution
  star-map showing that the concrete `innerρ₃` / `splitSource₃` /
  `splitTarget★₃` argument works over the generated window embeddings
  `κ₁` and `κ₂`.  Without that bridge, context entries cannot be built either,
  because their entry obligations are exactly the shifted versions of the same
  type-level transports.

Smallest next surface:

  Generalize the concrete body-obligation lemmas, not the relation:

    * define window-indexed variants of the source/target substitution maps
      used by `Λ-inner-body-⊑ᵂ` and `Λ-final-body-⊑ᵂ`;
    * prove their `embedᴸ`/`embedᴿ` equations against
      `ΛRouteOneMidWorldAt W W₂ κ₁ κ₂` and `liftWorldLeft X⊑★ W₂`;
    * prove the corresponding star-map from `ΛRouteOneWindowFacts`;
    * derive `innerBody⊑ᵂ` and `finalBody⊑ᵂ`, then build the context fields
      from those entry transports.

Checked state:

  The live tree remains green after the pushed center-geometry chunks:

    `AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
       -i GTSFImp/proof/DGG/notes -v0 GTSFImp/All.agda`

    `AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
       -i GTSFImp/proof/DGG/notes -v0 \
       GTSFImp/proof/DGG/notes/M5InstInversionDesignScratch.agda`

  No live relation was changed, and no postulate, hole, or catch-all was
  added.

RESOLVED 2026-08-12:

  The parameterized route-one support is now live and checked in
  `GTSFImp/proof/DGG/Catchup/InstInversionProof.agda`.

  The concrete-only body transports were generalized over the supplied target
  window embeddings and target insertion witnesses:

    `route1SplitSource`
    `route1SplitTarget★`
    `Λ-route1-inner-body-⊑ᵂ`
    `Λ-route1-final-body-⊑ᵂ`
    `Λ-route1-post-window-support-at`

  The missing mid-to-fresh monotonicity field is now:

    `Λ-route1-mid-fresh-mono-at`

  The smart pushout instances are now checked for both smart guard branches:

    `Λ-route1-smart-alias-facts`
    `Λ-route1-smart-alias-ext₂`
    `Λ-route1-smart-alias-post-window`
    `Λ-route1-smart-fresh-facts`
    `Λ-route1-smart-fresh-ext₂`
    `Λ-route1-smart-fresh-post-window`

  These instantiate `ΛPostWindowGeometry Wᵐ Wᵐ₂ extᵐ₂` at the target-inserted
  smart route-one worlds.  Therefore the ordinary `Λ⊑Λ²` leaf under a smart
  premise can now be closed by:

    `Λ⊑Λ²-base-prefix-at-base`

  with either `Λ-route1-smart-alias-post-window` or
  `Λ-route1-smart-fresh-post-window`.

  The next obstruction is no longer the route-one body transport.  It is the
  source-left recursive post-prefix surface needed by plain `Λ⊑²` and
  source-strip wrappers under a supplied smart post window.  See:

    `m5-inst-inversion-source-left-post-prefix-at-blocked.red`

Checked commands after resolution:

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
    -i GTSFImp/proof/DGG/notes -v0 \
    GTSFImp/proof/DGG/Catchup/InstInversionProof.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
    -i GTSFImp/proof/DGG/notes -v0 GTSFImp/All.agda
