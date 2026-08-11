M5 instantiation inversion blocker: lift-to-bind source-side rebase

Date: 2026-08-11

Blocked target:

  implementation of `Λ⊑Λ²PostBodyTransportᵀ`, specifically the
  relation-level conversion from

    CR.renameWorld wk↪ᵗ
      (liftWorldBoth X⊑X (rightOnlyWorld W ★))

  to the fresh target-bind world

    world
      (skip (keep (skip (ηᴸʷ W))))
      (skip (keep (keep (ηᴿʷ W))))
      (instᵐ (extendᵐ X⊑X (instᵐ (impEnvʷ W))))
      (store-lift (sourceStoreʷ W))
      (store-bind (store-bind (targetStoreʷ W) ★) (＇ zero)).

What was reused/built:

  Reused:

    CenterRename.⊢²-rename-center
    TypeInTermSubst.StoreTransport-lift-bind
    TypeInTermSubst.typing-store-transport

  Newly built and checked in `proof/DGG/TargetBindLift.agda`:

    ΛLiftToBindFreshWorld
    revealˣ-store-transport / concealˣ-store-transport
    revealˣ-pivot-store / concealˣ-pivot-store
    TargetStoreMove
    moveCtx / moveSameCtx / moveImpEnvMono
    liftMoveBoth / liftMoveLeft
    target-typing-move
    moveStoreRepWithTarget∈
    target-pivot RebaseAt transport helpers

  These support target-side reveal/conceal rebases because the indexed
  target conversion gives a store lookup for the target pivot. Under
  `store-lift`, that lookup rules out the fresh zero and proves the target
  canonical representation is unchanged by `StoreTransport-lift-bind`.

New resister:

  The source-side rebase constructors do not provide a target conversion
  premise:

    reveal⊑² ... (rebase-varᴸ rb) ... c⊢ M⊑M′ q
    conceal⊑² ... (tag-rebase-varᴸ rb) ... c⊢ M⊑M′ q

  Their `rb : RebaseAt W W′ Xᴸ Xᴿ` / `RebaseAt W′ W Xᴸ Xᴿ`
  contains:

    StoreRepImp W′ Xᴸ Xᴿ

  but there is no target-store lookup for `Xᴿ`. In the fresh lift-to-bind
  conversion, the problematic target pivot is the abstract target binder:

    Xᴿ = zero
    resolveVar (store-lift (store-bind Σ ★)) zero = ＇ zero
    resolveVar (store-bind (store-bind Σ ★) (＇ zero)) zero = ★

  So transporting `StoreRepImp` before decay requires changing the stored
  target representation from `＇ zero` to `★`:

    resolveVar sourceStore Xᴸ ⊑ᵂ ＇ zero
    ------------------------------------ ?
    resolveVar sourceStore Xᴸ ⊑ᵂ ★

  Under the pre-decay conversion world, the fresh aligned center is still
  marked `X⊑X`; the needed `X⊑★` evidence for the fresh alias does not
  exist. This is not a non-variable substitution problem, but it is a
  missing-evidence problem at exactly the source-side rebase constructors.

Why target-side cases are not the blocker:

  In `⊑reveal²`, `⊑conceal²`, `reveal⊑reveal²`,
  `conceal⊑conceal²`, and `packaged-seal-star²`, the target conversion
  premise is indexed at `just Xᴿ`. The checked `revealˣ-pivot-store` /
  `concealˣ-pivot-store` inversion provides a store entry for `Xᴿ`; with
  the old `store-lift` target store, that entry cannot be the fresh zero,
  so the canonical target representation is definitionally preserved by
  the fresh bind conversion.

Supervisor decision needed:

  The current approved composition order converts before decaying
  `X⊑X → X⊑★`. Source-side rebase-var needs the decay first, or a
  stronger theorem that supplies `resolveVar sourceStore Xᴸ ⊑ᵂ ★` for
  source rebases that park onto the fresh target binder. That would be a
  live design choice for the Λ post-body transport.

No live statement was weakened, and no postulate, hole, or catch-all was
added.
