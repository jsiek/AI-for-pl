M5 instantiation inversion blocker: left-lift/right-bind commuting

Date: 2026-08-11

Blocked target:

  the `Λ⊑²` recursive rewrap in `InstInversionPackage.Λ-package`

Phase A′ pre-flight extended `M5InstInversionDesignScratch.agda` with
the derivation-recursive statement:

  RecursiveΛInversionPreflight.derivation-recursive-Λ
  RecursiveΛInversionPreflight.Λ⊑²-rewrap

The one-sided rewrap checks as a statement, but expanding it requires
the statement-level commuting surface:

  LeftLiftRightBindPreflight.right-bind-under-left-lift

whose first field is the exact right-extension needed by the recursive
`Λ⊑²` rewrap:

  ECR.WorldExtendᴿ (bind B ∷ [])
    (CTI2.liftWorldLeft X⊑★ W)
    (CTI2.liftWorldLeft X⊑★ (CTI2.rightOnlyWorld W B))

The proven right-bind extension used by M5 has a different target when
instantiated under the left-lifted world:

  ECR.WorldExtendᴿ (bind B ∷ [])
    (CTI2.liftWorldLeft X⊑★ W)
    (CTI2.rightOnlyWorld (CTI2.liftWorldLeft X⊑★ W) B)

These two target worlds are not definitionally the same. Their center
embeddings place the source-only binder and the target-only binder in
opposite orders:

  CTI2.rightOnlyWorld (CTI2.liftWorldLeft X⊑★ W) B
    source embedding = skip (keep (ηᴸʷ W))

  CTI2.liftWorldLeft X⊑★ (CTI2.rightOnlyWorld W B)
    source embedding = keep (skip (ηᴸʷ W))

On the fresh source binder:

  toRenameᵗ (skip (keep η)) zero = suc zero
  toRenameᵗ (keep (skip η)) zero = zero

So the recursive body package lands in a world where the fresh source
binder is parked at center `suc zero`, while the parent rewrap needs the
world where that binder is parked at center `zero`. This is exactly the
left/right allocation-order issue the approved design called out.

The target typing premise for the rewrap is not the immediate blocker:
once a recursive post relation is available in the correct lifted
extended world, `CastTermImprecision2Typing.target-typing²` can rederive
the target typing of the post-application target. The blocker is getting
that recursive relation into the parent lifted world in the first place.

Smallest unblocking statement:

  a parked/center-swap commuting lemma relating
  `rightOnlyWorld (liftWorldLeft X⊑★ W) B` and
  `liftWorldLeft X⊑★ (rightOnlyWorld W B)`, including transport of
  term-imprecision derivations and lifted contexts across the swap.

Equivalently, the recursive Λ inversion package could expose its result
already transported through this swap, but that still requires the same
new geometry lemma. No live statement was weakened, and no postulate or
hole was added.
