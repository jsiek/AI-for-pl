M5 instantiation inversion blocker: Λ post-body target-store transport

Date: 2026-08-11

Blocked target:

  implementation of the specialized `Λ⊑Λ²PostBodyTransportᵀ` in
  `proof/DGG/Catchup/InstInversionProof.agda`.

Pre-flight status:

  The approved concrete surface is live and checks:

    W₂ = rightOnlyWorld (rightOnlyWorld W ★) (＇ zero)
    χs₂ = bind ★ ∷ bind (＇ zero) ∷ []

  `GTSFImp/proof/DGG/notes/M5InstInversionDesignScratch.agda` rechecks
  `Λ⊑Λ²-base-rewrap-preflight`, so the Λ base call site accepts the
  two-bind tower once the body transport exists.

Validated prefix:

  The first target insertion is accepted by Agda:

    TargetExtend.⊢²-target-insert
      (TargetExtend.keepRightBindTargetInsert {W = W} {B = ★}
        {v = X⊑X})
      bodyRel

  It produces the expected post-`β-Λ` body target term shape:

    liftWorldBoth X⊑X (rightOnlyWorld W ★) ∣ γ★
      ⊢² V ⊑ renameᵗᵐ (keep wk↪ᵗ) V′ ∶ p★

  with target store:

    store-lift (store-bind (targetStoreʷ W) ★)

New resister:

  The target body exposed by the catalogued `β-Λ` step lives in the
  two-bind post world:

    liftWorldLeft X⊑★
      (rightOnlyWorld (rightOnlyWorld W ★) (＇ zero))

  whose target store is:

    store-bind (store-bind (targetStoreʷ W) ★) (＇ zero)

  This is the same target arity as the first inserted body relation, but
  a different target store: preservation handles this shape for typing
  via `typing-lift-to-bind`, but the CTI2 relation has no corresponding
  derivation-level target-store transport.

  The other available transports do not cover this step:

  - `TermImpDecay.⊢²-decay` changes only imprecision marks between worlds
    with identical source and target stores.
  - `CenterRename.⊢²-rename-center` inserts center variables but leaves
    both stores unchanged.
  - applying `keepRightBindTargetInsert` a second time to the first
    inserted body extends the target term context once more, landing at a
    `suc (suc (suc Δᴿ))` target term, not at the post-`β-Λ` body context
    `suc (suc Δᴿ)`.
  - `WorldExtendᴿ` transports obligations and contexts, but not arbitrary
    `_∣_⊢²_⊑_∶_` derivations across the lifted-store-to-bound-store
    replacement.

Smallest unblocking theorem:

  add a relation-level analogue of `typing-lift-to-bind`, specialized
  enough for the post-`β-Λ` target body:

    liftWorldBoth X⊑X (rightOnlyWorld W ★) ∣ γ★
      ⊢² V ⊑ renameᵗᵐ (keep wk↪ᵗ) V′ ∶ p★
    ------------------------------------------------------------
    Wᵖ ∣ γᵖ
      ⊢² V ⊑ renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵖ

  where `Wᵖ` has the post-`β-Λ` target store
  `store-bind (store-bind (targetStoreʷ W) ★) (＇ zero)` and the
  source/target embeddings needed by the generated `RebaseAtᴿ` reveal
  premise.  The proof likely needs indexed conversion store transport
  for `_⊢↑[_]_`/`_⊢↓[_]_` plus preservation of the rebase/store
  representation side conditions.

No live statement was weakened, and no postulate, hole, or catch-all was
added.

Postscript 2026-08-11:

  RESOLVED/REFINED by `proof/DGG/TargetBindLift.agda` plus
  `m5-inst-inversion-lift-to-bind-source-rebase-blocked.red`.

  The fresh lift-to-bind world, indexed conversion store transport,
  target-pivot store inversion, target typing transport, and target-side
  rebase transport foundations now check. The remaining obstruction is
  narrower: source-side `rebase-varᴸ` / `tag-rebase-varᴸ` can park a
  source pivot onto the fresh abstract target binder without any target
  conversion premise, so converting before `X⊑X → X⊑★` decay lacks the
  representation evidence for `★`.
