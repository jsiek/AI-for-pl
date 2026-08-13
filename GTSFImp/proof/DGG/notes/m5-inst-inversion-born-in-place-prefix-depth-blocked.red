M5 instantiation inversion blocker: born-in-place source-left prefix depth

Status: BLOCKED, 2026-08-13.

Context:

  The previous source-left attempt framed the remaining gap as a swap of the
  abstract target binder past a source-only binder.  The correct retry is the
  born-in-place route: generated target centers should be introduced at their
  final positions under the source-left prefix, not moved there later.

  The checked support before this retry remains:

    `TargetBindLift.freshLiftToBindTargetMoveAtκᴸ`
    `ΛRouteOneFreshWorldAtᴸ`
    `Λ-route1ᴸ-prefix-at`

  These validate the source-left first target-bind transport when the route is
  allowed to keep the live `liftWorldBoth (liftWorldLeft W)` center order.

Candidate born-in-place surface:

  At prefix depth `k = 1`, the caller's post body world for the recursive
  `Λ⊑Λ²` leaf is:

    `liftWorldLeft X⊑★
       (liftWorldLeft X⊑★
         (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero)))`

  So the generated target pivot must be born below both source-left centers.
  In the concrete center order, the relevant final placements are:

    source binder for the rewrapped `Λ` : center `zero`
    existing source-left prefix binder  : center `suc zero`
    generated target slot `zero`       : center `suc (suc zero)`

  A prefix-depth source-left route-one geometry would therefore need its
  fresh/mid/out worlds to have `ηᴿ zero = suc (suc zero)` from the start.

Exact failing field:

  The first inexpressible field is the source-left companion of
  `ΛPostWindowGeometry.route1Prefix`.

  The live `Λ⊑Λ²` constructor supplies its body premise at:

    `liftWorldBoth X⊑X (liftWorldLeft X⊑★ W)`

  In that premise world, the inner source binder and the inner target binder
  share the same `X⊑X` center:

    `ηᴸ zero = zero`
    `ηᴿ zero = zero`

  and the existing source-left prefix center is already after it:

    `ηᴸ (suc zero) = suc zero`

  The born-in-place output would have to use the same premise relation while
  placing the source side of that shared center at `zero` and the target side
  of that same center at `suc (suc zero)`, with the source-prefix center
  between them.

  That is not merely unproven.  It is not expressible by the existing world
  evolution vocabulary:

    * `TargetStoreMove` preserves both `ηᴸ` and `ηᴿ` definitionally.
    * `CenterRename` / `_↪ᵗ_` maps one old center to one new center; it cannot
      split a shared `X⊑X` center into distinct source and target centers.
    * An order-preserving embedding also cannot send the old shared center
      past the old source-prefix center on the target side while leaving it
      before that prefix on the source side.
    * `TargetInsert` and `WorldExtendᴿ` only add target-store slots and
      transport existing centers through a single old-center map; they do not
      split aligned centers.

  If `route1Prefix` were restated to take a born-in-place premise relation
  instead, the reveal fields could be stated with target embeddings frozen at
  prefix depth.  But that premise is not the premise produced by the live
  `Λ⊑Λ²` constructor, so it would require a new relation rule or a generalized
  `Λ⊑Λ²` premise world.  The alternative is the forbidden/refuted exchange
  transport.

Consequences:

  The reveal fields are not the first obstruction.  At prefix depth they are
  reachable only after replacing the live `Λ⊑Λ²` body-premise field with a
  born-in-place premise.  Therefore the plain `Λ⊑²` branch under a smart
  premise, the source-strip wrappers that recurse through it, and
  `InstInversionPackage.Λ-package` cannot be closed with proof-surface changes
  alone.

  This is a smart-comma-scale one-sided finding: the current live relation has
  no constructor whose premise world births the `Λ⊑Λ²` target binder under an
  existing source-left prefix.

Checked state:

  Before recording this note, the live tree was green at commit `85ce1eb`:

    AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
      -i GTSFImp/proof/DGG/notes -v0 GTSFImp/All.agda

  No live relation was changed, and no postulate, hole, or catch-all was
  added.
