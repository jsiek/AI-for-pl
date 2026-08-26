M5 instantiation inversion blocker: smart route-one needs the full target
window embedding

Date: 2026-08-12

Context:

  The first part of the approved smart route-one direction is now live in
  `TargetBindLift`:

    `freshLiftToBindTargetMoveAt`
    `freshLiftToBindTargetMoveAtκ`

  The second theorem is the needed generalization of the concrete
  `freshLiftToBindTargetMove★`: the caller supplies the center embedding for
  the route-one world, the dynamic pivot mark, and the final target-store
  resolver facts.

Checked result:

  `TargetBindLift.agda` and `All.agda` both check after these support
  helpers, and the commits are pushed:

    `6765cc1 Generalize route-one target bind move`
    `eaf36cc Parameterize route-one target bind move`

New resister:

  Instantiating `ΛPostWindowGeometry Wᵐ Wᵐ₂ extᵐ₂` for the smart premise
  needs more center geometry than the current approved scratch surface
  exposes:

    `SmartCommaLiftᴸ W Wᵐ`
    `TargetInsert wk↪ᵗ πᵐ₁ Wᵐ Wᵐ₁`
    `TargetInsert wk↪ᵗ πᵐ₂ Wᵐ₁ Wᵐ₂`
    `SmartCommaLiftᴸ
       (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero)) Wᵐ₂`

  The second `TargetInsert` exposes only the old-center injection:

    `πᵐ₂ : Δᵐ₁ ↪ᵗ Δᵐ₂`

  but the route-one `freshWorld` must use an embedding for the whole
  generated target window:

    `κᵐ₂ : suc Δᵐ₁ ↪ᵗ Δᵐ₂`

  and the route-one center rename is then:

    `skip κᵐ₂ : suc Δᵐ₁ ↪ᵗ suc Δᵐ₂`

  This is what makes the target embedding of the route-one fresh world match
  the target embedding of `liftWorldLeft X⊑★ Wᵐ₂`:

    `toRenameᵗ (skip κᵐ₂)
       (toRenameᵗ (ηᴿʷ (liftWorldBoth X⊑★ Wᵐ₁)) Y)
     ≡
     toRenameᵗ (ηᴿʷ (liftWorldLeft X⊑★ Wᵐ₂)) Y`

  In the concrete right-only instance, `κᵐ₂ = id↪ᵗ`, so
  `skip κᵐ₂ = wk↪ᵗ`, exactly the old `freshLiftToBindTargetMove★` layout.

  In the smart-fresh pushout instance, `κᵐ₂` is the `old′` embedding produced
  by:

    `embeddingPushout πᵐ₂ oldCenters`

  while `πᵐ₂` is the pushout `premise` embedding for old centers.  These are
  different fields of the pushout.  The current `TargetInsert` record keeps
  `πᵐ₂` but does not expose `old′`, so the route-one target embedding cannot
  be stated from the existing arguments.

Why this is not just proof plumbing:

  Choosing `keep πᵐ₂` would keep the abstract target-lift center at the new
  front source center, so the inner reveal pivot would not share the target
  embedding of the generated alias slot in `liftWorldLeft X⊑★ Wᵐ₂`.

  Choosing `skip πᵐ₂` works only for the concrete/front insertion where the
  generated target slot's center is literally `zero`.  It is wrong for the
  pushout smart-fresh case, where the generated target slot is embedded by
  `old′ zero`.

Smallest next surface:

  Extend the smart route-one post-window support theorem, not the relation,
  with a supplied/generated full-window embedding for the second target bind:

    `κᵐ₂ : suc Δᵐ₁ ↪ᵗ Δᵐ₂`

  together with its target-window equations and the dynamic mark/store facts
  consumed by `freshLiftToBindTargetMoveAtκ`.

  The constructors should derive `κᵐ₂` closed-world:

    * concrete/right-only: `κᵐ₂ = id↪ᵗ`;
    * smart-alias target insert: `κᵐ₂ = id↪ᵗ` for the concrete inserted
      center context;
    * smart-fresh target insert: `κᵐ₂ = EmbeddingPushout.old′ po`.

  After that, the `freshWorld` can be stated as:

    `targetStoreAs
       (renameWorld (skip κᵐ₂) (liftWorldBoth X⊑★ Wᵐ₁))
       (targetStoreʷ Wᵐ₂)`

  and the remaining `midWorld`/outer rebase fields should be built around the
  same `κᵐ₂` window.

Checked state:

  The live tree remains green:

    `AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
       -i GTSFImp/proof/DGG/notes -v0 GTSFImp/All.agda`

    `AGDA_DIR=/tmp/agda-work/agda-home agda -i GTSFImp \
       -i GTSFImp/proof/DGG/notes -v0 \
       GTSFImp/proof/DGG/notes/M5InstInversionDesignScratch.agda`

  No live relation was changed, and no postulate, hole, or catch-all was
  added.
