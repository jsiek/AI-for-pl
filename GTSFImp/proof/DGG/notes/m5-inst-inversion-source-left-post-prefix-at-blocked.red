M5 instantiation inversion blocker: source-left post-prefix at a supplied
smart post window

Status: BLOCKED, 2026-08-12.

Context:

  The route-one post-window package for the ordinary `Λ⊑Λ²` leaf now checks at
  target-inserted smart premise worlds.  The live witnesses are:

    `Λ-route1-smart-alias-post-window`
    `Λ-route1-smart-fresh-post-window`

  Consequently, if a smart premise derivation reaches:

    `Λ⊑Λ² liftγ vV vV′ bodyRel q`

  the base prefix can be built at the smart post world by:

    `Λ⊑Λ²-base-prefix-at-base`

  using the appropriate smart post-window geometry.

New resister:

  Assembling the full derivation-recursive prefix worker requires more than
  the `Λ⊑Λ²` leaf.  Under a smart-comma source case:

    `Λ⊑²-smart-comma Anv zero∈A liftW liftγ vV target⊢ bodyRel q`

  the recursive call on `bodyRel` must produce:

    `ΛPostPrefixPackageAtBase bodyRel extᵐ₂ c′ B′≢★`

  at the target-inserted smart premise post world `Wᵐ₂`.

  The `Λ⊑Λ²` branch of that recursive call is now covered, but the worker also
  has to handle these shapes inside the smart premise:

    `Λ⊑²`
    `Λ⊑²-smart-comma`
    `cast⊑²`
    `reveal⊑²`
    `conceal⊑²`

  The plain `Λ⊑²` branch needs a prefix package for its body at the
  source-left premise world:

    `liftWorldLeft X⊑★ Wᵐ`

  over the supplied smart post window.  The concrete helper has exactly this
  shape only for the hard-coded concrete post world:

    `right-bind-right-bind-world-extendᴿ {W = liftWorldLeft X⊑★ Wᵐ}`

  and the old fixed smart-front world.  It does not provide the corresponding
  `WorldExtendᴿ`, context transport, target typing equality, or relation
  rewrap for the supplied pushout-indexed `Wᵐ₂`.

  The source-strip branches need the same missing source-left surface through
  their post obligation.  The live concrete extractor:

    `Λ-strip-prefix-p₂`

  derives:

    `A ⊑ᵂ⟨ rightOnlyWorld (rightOnlyWorld W ★) (＇ zero) ⟩
       ΛResidualSource₂ B`

  from `A ⊑ᵂ⟨ W ⟩ `∀ B`, but it is fixed to the concrete right-only post
  world.  A parameterized version for arbitrary `W₂` must handle the `∀⊑`
  view by recursing through the same source-left post-prefix geometry.

Why this is a real surface gap:

  `ΛPostWindowGeometry W W₂ ext₂` is enough for the ordinary `Λ⊑Λ²` base
  transport.  Its fields expose the route-one fresh/mid/out worlds needed to
  build the two generated target reveals from a `liftWorldBoth X⊑X W` body
  premise.

  It does not expose a companion post-prefix route for:

    `liftWorldLeft X⊑★ W`

  nor an `At` version of the source-strip post obligation:

    `Λ-strip-prefix-p₂-at :
       A ⊑ᵂ⟨ W ⟩ `∀ B
       → A ⊑ᵂ⟨ W₂ ⟩ ΛResidualSource₂ B`

  for the supplied smart `W₂`.

Smallest next surface:

  Add a source-left post-prefix companion for a supplied two-allocation post
  window.  It should carry the source-left post `WorldExtendᴿ`, context
  transport, target context equality, and the parameterized post obligation
  needed by plain `Λ⊑²` and by `cast⊑²` / `reveal⊑²` / `conceal⊑²`.

  This is a proof-surface extension only.  It does not require changing
  `Λ⊑²-smart-comma` or any live relation constructor.

Checked state before stopping:

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
    -i GTSFImp/proof/DGG/notes -v0 \
    GTSFImp/proof/DGG/Catchup/InstInversionProof.agda

  AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
    -i GTSFImp/proof/DGG/notes -v0 GTSFImp/All.agda

No live relation was changed, and no postulate, hole, or catch-all was added.

Continuation attempt, 2026-08-13:

  The first target-bind part of the source-left companion is not the blocker.
  The following support now checks:

    `TargetBindLift.freshLiftToBindTargetMoveAtκᴸ`
    `ΛRouteOneFreshWorldAtᴸ`
    `Λ-route1ᴸ-prefix-at`

  The checked prefix transports a `Λ⊑Λ²` body premise under an existing
  source-left lift through the first generated target bind, decay,
  `renameWorld (skip (keep κ₂))`, and the source-left `TargetBindLift`
  move.  This validates the one-sided shadow of the route-one fresh step.

  The obstruction reappears at the reveal geometry.  The source-left fresh
  route embeds the abstract target pivot before the existing source-left
  center.  In the concrete notation from the old lifted-pivot note, the
  fresh route has the target variable `zero` at center `suc zero`:

    `ηᴿ(ΛLiftToBindFreshWorldᴸ X⊑★ W) zero = suc zero`

  The caller-supplied post world required by the recursive prefix is:

    `liftWorldLeft X⊑★
       (liftWorldLeft X⊑★
         (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero)))`

  and in that world the same generated target variable is after both
  source-left binders:

    `ηᴿ(...) zero = suc (suc zero)`

  A `ΛPostWindowGeometry` companion would need both generated reveal rebuilds
  to use `RebaseAtᴿ`.  Its `ηᴿ-frozen` field freezes every target variable,
  so the target embeddings of the fresh/mid/out worlds must agree on `zero`.
  The two placements above therefore cannot be connected by the existing
  reveal rule or by `TargetBindLift.TargetStoreMove`, which also preserves
  `ηᴿ`.

  This is the same order-preserving center obstruction recorded in
  `m5-inst-inversion-lambda-lifted-target-pivot-blocked.red`, now localized
  to the approved source-left companion surface.  The smart-comma guard and
  target-insert transports handle the smart premise world after the two target
  binds, but they do not supply a relation-level transport that swaps the
  abstract `liftWorldBoth` target binder past an existing source-only binder.

  Checked before stopping:

    AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
      -i GTSFImp/proof/DGG/notes -v0 GTSFImp/All.agda

  No live relation was changed, and no postulate, hole, or catch-all was
  added.

Born-in-place refinement, 2026-08-13:

  The no-swap retry is recorded in:

    `m5-inst-inversion-born-in-place-prefix-depth-blocked.red`

  It isolates the exact first field that cannot be inhabited with the current
  live relation: the source-left prefix-depth companion of
  `ΛPostWindowGeometry.route1Prefix`.  The reveal fields themselves can be
  stated for born-in-place worlds, but the live `Λ⊑Λ²` constructor supplies a
  body premise whose source and target binders share one `X⊑X` center before
  the prefix.  The born-in-place route needs that center split around the
  source-left prefix, which is not expressible by `_↪ᵗ_`, `TargetStoreMove`,
  `TargetInsert`, or `WorldExtendᴿ`.
