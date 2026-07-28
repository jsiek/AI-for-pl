module proof.Right.Core.NuImprecisionPairedConversionTransportProof where

-- File Charter:
--   * Transports exact live paired-reveal and paired-conceal constructor
--     evidence through one completed keep-leading result and store lineage.
--   * States both constructor-shaped theorems directly; endpoint syntax is
--     never treated as evidence that a paired constructor was used.
--   * Contains no silent-result premise, widening transport, retired
--     `PairedCast` abstraction, dispatcher, postulate, hole, or permissive
--     option.

open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using ([])
open import Data.Product using
  (_,_; _×_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyCoercion; applyTy; applyTyCtxs; applyTys; keep)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  )
open import Relation.Binary.PropositionalEquality using
  (subst; sym)
open import Types using (Ty; TyCtx; TyVar)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; targetCtxResult
  ; targetStoreResult
  ; targetTailChanges
  ; transportType
  )
open import proof.Core.Properties.NuConversionTransport using
  ( apply-conceal-conversions-exact
  ; apply-reveal-conversions-exact
  )
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyTyVars)
open import
  proof.Left.SilentTransport.NuImprecisionLeftSilentConversionEndpointTransport
  using (result-source-conceal; result-source-reveal)
open import
  proof.Store.Lineage.NuImprecisionStoreCorrespondsLineageTransportProof
  using (store-corresponds-lineage-transportᵀ)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using (transport-paired-replacement)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (WeakOneStepStoreLineage)


private
  result-target-reveal :
    ∀ {Φ Δᴸ Δᴿ M M′ C C′ μ β X c A B}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
    RevealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X c A B →
    ∃[ μ′ ]
      RevealConversion μ′
        (resultRightCtx inner)
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) β)
        (applyTys (targetTailChanges inner) X)
        (applyCoercions (targetTailChanges inner) c)
        (applyTys (targetTailChanges inner) A)
        (applyTys (targetTailChanges inner) B)
  result-target-reveal
      {Δᴿ = Δᴿ} {β = β} {X = X} {c = c} {A = A} {B = B}
      prefix inner c↑ =
    final-mode , final
    where
    applied =
      apply-reveal-conversions-exact
        {χs = targetTailChanges inner}
        (weaken-reveal-conversion
          (rightStoreⁱ-prefix-inclusion prefix) c↑)

    final-mode = proj₁ applied

    final =
      subst
        (λ Δ → RevealConversion final-mode Δ
          (rightStoreⁱ (resultStore inner))
          (applyTyVars (targetTailChanges inner) β)
          (applyTys (targetTailChanges inner) X)
          (applyCoercions (targetTailChanges inner) c)
          (applyTys (targetTailChanges inner) A)
          (applyTys (targetTailChanges inner) B))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → RevealConversion final-mode
            (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ
            (applyTyVars (targetTailChanges inner) β)
            (applyTys (targetTailChanges inner) X)
            (applyCoercions (targetTailChanges inner) c)
            (applyTys (targetTailChanges inner) A)
            (applyTys (targetTailChanges inner) B))
          (sym (targetStoreResult inner))
          (proj₂ applied))

  result-target-conceal :
    ∀ {Φ Δᴸ Δᴿ M M′ C C′ μ β X c A B}
      {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
    StoreImpPrefix ρ₀ ρ⁺ →
    (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
    ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀) β X c A B →
    ∃[ μ′ ]
      ConcealConversion μ′
        (resultRightCtx inner)
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) β)
        (applyTys (targetTailChanges inner) X)
        (applyCoercions (targetTailChanges inner) c)
        (applyTys (targetTailChanges inner) A)
        (applyTys (targetTailChanges inner) B)
  result-target-conceal
      {Δᴿ = Δᴿ} {β = β} {X = X} {c = c} {A = A} {B = B}
      prefix inner c↓ =
    final-mode , final
    where
    applied =
      apply-conceal-conversions-exact
        {χs = targetTailChanges inner}
        (weaken-conceal-conversion
          (rightStoreⁱ-prefix-inclusion prefix) c↓)

    final-mode = proj₁ applied

    final =
      subst
        (λ Δ → ConcealConversion final-mode Δ
          (rightStoreⁱ (resultStore inner))
          (applyTyVars (targetTailChanges inner) β)
          (applyTys (targetTailChanges inner) X)
          (applyCoercions (targetTailChanges inner) c)
          (applyTys (targetTailChanges inner) A)
          (applyTys (targetTailChanges inner) B))
        (sym (targetCtxResult inner))
        (subst
          (λ Σ → ConcealConversion final-mode
            (applyTyCtxs (targetTailChanges inner) Δᴿ) Σ
            (applyTyVars (targetTailChanges inner) β)
            (applyTys (targetTailChanges inner) X)
            (applyCoercions (targetTailChanges inner) c)
            (applyTys (targetTailChanges inner) A)
            (applyTys (targetTailChanges inner) B))
          (sym (targetStoreResult inner))
          (proj₂ applied))


paired-reveal-evidence-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ A A′ B B′ X X′ : Ty}
    {c c′} {α β : TyVar} {μ μ′}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  WeakOneStepTypeCoherence inner →
  WeakOneStepStoreLineage inner →
  StoreCorresponds ρ₀ α X β X′ pX →
  RevealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
  RevealConversion μ′ Δᴿ (rightStoreⁱ ρ₀) β X′ c′ A′ B′ →
  p [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ q →
  Σ[ pX′ ∈ (resultCtx inner ∣ resultLeftCtx inner
      ⊢ applyTys (sourceChanges inner) X
        ⊑ applyTys (targetTailChanges inner) X′
        ⊣ resultRightCtx inner) ]
  ∃[ μˢ ]
  ∃[ μᵗ ]
    StoreCorresponds
      (resultStore inner)
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyTyVars (targetTailChanges inner) β)
      (applyTys (targetTailChanges inner) X′)
      pX′
    × RevealConversion μˢ
        (resultLeftCtx inner)
        (leftStoreⁱ (resultStore inner))
        (applyTyVars (sourceChanges inner) α)
        (applyTys (sourceChanges inner) X)
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B)
    × RevealConversion μᵗ
        (resultRightCtx inner)
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) β)
        (applyTys (targetTailChanges inner) X′)
        (applyCoercions (targetTailChanges inner) c′)
        (applyTys (targetTailChanges inner) A′)
        (applyTys (targetTailChanges inner) B′)
    × ((transportType inner p)
        [ applyTyVars (sourceChanges inner) α
        ↦ applyTys (sourceChanges inner) X
        ⊑⟨ pX′ ⟩
        applyTys (targetTailChanges inner) X′
        ↤ applyTyVars (targetTailChanges inner) β ]ᴾ
      (transportType inner q))
paired-reveal-evidence-transportᵀ
    prefix inner type-coherence lineage
    corr c↑ c′↑ replacement
    with store-corresponds-lineage-transportᵀ
           prefix inner lineage corr
       | result-source-reveal prefix inner c↑
       | result-target-reveal prefix inner c′↑
paired-reveal-evidence-transportᵀ
    prefix inner type-coherence lineage
    corr c↑ c′↑ replacement
    | pX , corr′ , pX-shape | μ , cˢ↑ | μ′ , cᵗ↑ =
  pX , μ , μ′ ,
  corr′ , cˢ↑ , cᵗ↑ ,
  transport-paired-replacement
    inner type-coherence replacement pX pX-shape


paired-conceal-evidence-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ A A′ B B′ X X′ : Ty}
    {c c′} {α β : TyVar} {μ μ′}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  WeakOneStepTypeCoherence inner →
  WeakOneStepStoreLineage inner →
  StoreCorresponds ρ₀ α X β X′ pX →
  ConcealConversion μ Δᴸ (leftStoreⁱ ρ₀) α X c A B →
  ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ₀) β X′ c′ A′ B′ →
  q [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ p →
  Σ[ pX′ ∈ (resultCtx inner ∣ resultLeftCtx inner
      ⊢ applyTys (sourceChanges inner) X
        ⊑ applyTys (targetTailChanges inner) X′
        ⊣ resultRightCtx inner) ]
  ∃[ μˢ ]
  ∃[ μᵗ ]
    StoreCorresponds
      (resultStore inner)
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyTyVars (targetTailChanges inner) β)
      (applyTys (targetTailChanges inner) X′)
      pX′
    × ConcealConversion μˢ
        (resultLeftCtx inner)
        (leftStoreⁱ (resultStore inner))
        (applyTyVars (sourceChanges inner) α)
        (applyTys (sourceChanges inner) X)
        (applyCoercions (sourceChanges inner) c)
        (applyTys (sourceChanges inner) A)
        (applyTys (sourceChanges inner) B)
    × ConcealConversion μᵗ
        (resultRightCtx inner)
        (rightStoreⁱ (resultStore inner))
        (applyTyVars (targetTailChanges inner) β)
        (applyTys (targetTailChanges inner) X′)
        (applyCoercions (targetTailChanges inner) c′)
        (applyTys (targetTailChanges inner) A′)
        (applyTys (targetTailChanges inner) B′)
    × ((transportType inner q)
        [ applyTyVars (sourceChanges inner) α
        ↦ applyTys (sourceChanges inner) X
        ⊑⟨ pX′ ⟩
        applyTys (targetTailChanges inner) X′
        ↤ applyTyVars (targetTailChanges inner) β ]ᴾ
      (transportType inner p))
paired-conceal-evidence-transportᵀ
    prefix inner type-coherence lineage
    corr c↓ c′↓ replacement
    with store-corresponds-lineage-transportᵀ
           prefix inner lineage corr
       | result-source-conceal prefix inner c↓
       | result-target-conceal prefix inner c′↓
paired-conceal-evidence-transportᵀ
    prefix inner type-coherence lineage
    corr c↓ c′↓ replacement
    | pX , corr′ , pX-shape | μ , cˢ↓ | μ′ , cᵗ↓ =
  pX , μ , μ′ ,
  corr′ , cˢ↓ , cᵗ↓ ,
  transport-paired-replacement
    inner type-coherence replacement pX pX-shape
