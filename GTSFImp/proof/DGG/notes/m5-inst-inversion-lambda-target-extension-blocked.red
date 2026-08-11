M5 instantiation inversion blocker: Λ base target-extension transport

Date: 2026-08-11

Blocked target:

  the implementation of the checked
  `Λ⊑Λ²PostBodyTransportᵀ` surface in
  `proof/DGG/Catchup/InstInversionDef.agda`.

Pre-flight status:

  `M5InstInversionDesignScratch.agda` now imports the live
  `Λ⊑Λ²PostBodyTransportᵀ` statement and checks:

    Λ⊑Λ²-base-rewrap-preflight :
      Λ⊑Λ²PostBodyTransportᵀ → ...

  The checked rewrap confirms that, once the transport returns the
  post body relation and the aligned top obligation, the `Λ⊑Λ²` base
  case can rebuild the required one-sided `Λ⊑²` relation at the caller's
  indexed post world.

Implementation resister:

  The first missing leg is not the target reveal rebase itself.  The
  generated target reveals are pivoted, but `⊑reveal²` can use
  `RebaseAtᴿ` premise worlds that move the source pivot to the target
  pivot center.  The `X⊑★` marks introduced by the right allocations are
  the intended store-representation witnesses for those rebases.

  Before either reveal can be rebuilt, the body premise must be transported
  from the original target binder context:

    bodyRel :
      liftWorldBoth X⊑X W ∣ γᴮ
        ⊢² V ⊑ V′ ∶ body-p

  to the post-`β-Λ` target body, schematically:

    liftWorldLeft X⊑★ W₂ ∣ γ₂ᴸ
      ⊢² V ⊑ renameᵗᵐ (keep wk↪ᵗ) V′ ∶ base-p₂

  where:

    W₂ = rightOnlyWorld (rightOnlyWorld W ★) (＇ zero)

  This is a target type-store extension/weakening of the *derivation*.
  Existing machinery does not supply it:

  - `TermImpDecay.⊢²-decay` only changes marks between worlds with the
    same source and target type contexts.
  - `CenterRename.⊢²-rename-center` only injects the center context; it
    leaves source and target term contexts and terms unchanged.
  - `ExtraCastRight2.WorldExtendᴿ` transports obligations and contexts,
    but has no theorem transporting `_∣_⊢²_⊑_∶_` derivations or target
    terms through a `StoreChanges` extension.
  - `WorldSupport.agda` explicitly leaves derivation-level world transport
    to a later stage.

Concrete missing theorem shape:

  a target-side store-change transport for CTI2 derivations, specialized
  enough to insert the instantiation `★` binder underneath the already
  visible target Λ binder:

    liftWorldBoth X⊑X W ∣ γᴮ
      ⊢² V ⊑ V′ ∶ body-p
    ------------------------------------------------------------
    liftWorldLeft X⊑★ W₂ ∣ γ₂ᴸ
      ⊢² V ⊑ renameᵗᵐ (keep wk↪ᵗ) V′ ∶ base-p₂

  plus the corresponding transported context, body obligation, and top
  `∀` obligation returned by `Λ⊑Λ²PostBodyTransportᵀ`.

Smallest unblocking work:

  add and prove a derivation-level target-extension transport theorem
  for CTI2, probably near the world-support/decay infrastructure rather
  than in the catch-up leaf.  Once that theorem exists, the remaining
  base transport should compose the mark decay, two target reveal rebases,
  target typing by `CastTermImprecision2Typing`, and the already checked
  `Λ⊑Λ²-base-rewrap-preflight`.

No live statement was weakened, and no postulate or hole was added.
