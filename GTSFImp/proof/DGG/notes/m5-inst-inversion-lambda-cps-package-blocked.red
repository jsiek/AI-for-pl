M5 instantiation inversion blocker: Λ CPS package indexing

Date: 2026-08-11

Blocked target:

  the derivation-recursive implementation of
  `InstInversionPackage.Λ-package`

Resolved before this blocker:

  `right-bind-under-left-lift` is now proved directly, and
  `Λ⊑²CPSRewrapᵀ` proves the one-sided `Λ⊑²` relation rewrap when the
  recursive body relation is already stated at the pre-built lifted
  extension tower:

    liftWorldLeft X⊑★ (rightOnlyWorld W Balloc)
      ∣ mapCtxᴿ right-bind-under-left-lift γᴸ
      ⊢² V ⊑ post ∶ body-p

The remaining package-level obstruction is that the recursive result
cannot be an arbitrary `InstPostCatalogPackage`.  In the `Λ⊑²` case,
the parent package must rebuild through:

  CTI2.Λ⊑² Anv zero∈A
    (mapCtxᴿ-liftᴸ parent-ext liftγ)
    vV target⊢ bodyRel p₂

where `bodyRel` must live specifically in:

  liftWorldLeft X⊑★ W₂

and its context must be the result of the pre-built lifted extension
tower over the parent extension `ext₂ : WorldExtendᴿ χs W W₂`.

But an `InstPostCatalogPackage` returned by the recursive body call hides
its post world existentially:

  Σ[ Δᴿ₂ ∈ TyCtx ] Σ[ χs₂ ∈ StoreChanges Δᴿ Δᴿ₂ ]
  Σ[ Δ₂ ∈ TyCtx ] Σ[ W₂ ∈ World ... ]
  Σ[ ext₂ ∈ WorldExtendᴿ χs₂ W W₂ ] ...

For the body recursion, that existential world has source context
`suc Δᴸ`; the parent rewrap needs evidence that it is exactly the
left-lift of the parent post world, and that its extension is exactly the
lifted tower.  The current package does not retain those equalities or an
index tying the recursive result to a caller-supplied extension tower.

Smallest unblocking statement:

  add an extension-indexed CPS post-catalog result for the Λ core worker:
  the caller supplies the parent right-extension and the corresponding
  lifted tower, and the recursive worker returns post relation, residual
  provenance, descent, and finish data at those specified worlds.  A
  projection can then package the top-level result back into the existing
  existential `InstPostCatalogPackage`.

No live statement was weakened, and no postulate or hole was added.

RESOLVED (2026-08-11): the live `InstPostCatalogPackageAt` is indexed by
the caller-supplied `χs₂`, `W₂`, and `ext₂`, so the recursive result no
longer hides the post-catalog world.  The root bridge
`inst-post-at→root-package` discharges the existential once, after
`inst-post-at-finish` composes the indexed prefix-to-residual trace with
the smaller extra-cast worker.  The next resister is the `Λ⊑Λ²`
post-catalog body transport, recorded separately in
`m5-inst-inversion-lambda-base-post-blocked.red`.
