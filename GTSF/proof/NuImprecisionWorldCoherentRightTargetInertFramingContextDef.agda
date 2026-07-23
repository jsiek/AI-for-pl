module
  proof.NuImprecisionWorldCoherentRightTargetInertFramingContextDef
  where

-- File Charter:
--   * Defines inert target-cast framing with the target-only context and
--     store-lineage witnesses exposed.
--   * Shares one contextual boundary across reveal, conceal, narrowing,
--     widening, and identity-mode widening evidence.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using
  (Coercion; Inert; id-onlyᵈ)
open import Conversion using
  (ConcealConversion; RevealConversion)
open import Data.Product using
  (_×_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using
  (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  (StoreImpPrefix)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx)
open import proof.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.NuImprecisionSimulationResultDef using
  (resultCtx; resultStore; targetTailChanges; weakIndexedResult)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  (lineageStore)
open import
  proof.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightTargetInertFramingContextᵀ : Set₁
WorldCoherentRightTargetInertFramingContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A A′ B′ : Ty} {c : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  Inert c →
  ((∃[ μ ] ∃[ β ] ∃[ X′ ]
      RevealConversion μ Δᴿ (rightStoreⁱ ρ₀)
        β X′ c A′ B′)
   ⊎
   (∃[ μ ] ∃[ β ] ∃[ X′ ]
      ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀)
        β X′ c A′ B′)
   ⊎
   (∃[ μ ]
      CastMode μ ×
      SealModeStore★ μ (rightStoreⁱ ρ₀) ×
      (μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ c ∶ A′ ⊒ B′))
   ⊎
   (∃[ μ ]
      CastMode μ ×
      SealModeStore★ μ (rightStoreⁱ ρ₀) ×
      (μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ c ∶ A′ ⊑ B′))
   ⊎
   (SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) ×
    (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
      ⊢ c ∶ A′ ⊑ B′))) →
  (inner : WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p) →
  resultCtx
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult inner)))
    ≡
    applyRightImpCtxChanges
      (targetTailChanges
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult inner))))
      Φ →
  RightOnlyStoreImpPrefix
    (lineageStore (worldRightCatchupStoreLineage inner))
    (resultStore
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult inner)))) →
  Σ[ framed ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult framed)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult framed))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage framed))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult framed))))
