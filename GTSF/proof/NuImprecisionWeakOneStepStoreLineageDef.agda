module proof.NuImprecisionWeakOneStepStoreLineageDef where

-- File Charter:
--   * Defines relational-store lineage for a weak one-step result.
--   * Factors lineage into renaming of every old relational entry followed
--     by a prefix of newly allocated entries.
--   * States the lineage-aware correspondence-transport boundary.
--   * Contains no simulation, lineage construction, or transport proof.

open import Data.List using (_∷_)
open import Data.Product using (∃-syntax)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyTys; keep)
open import NuTermImprecision using
  (StoreCorresponds; StoreImp)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  (StoreImpPrefix)
open import Types using (Ty; TyCtx; TyVar)
open import proof.NuImprecisionRelStoreEmbeddingDef using
  (RelStoreEmbeddingⁱ)
open import proof.NuImprecisionSimulationResultDef using
  ( LeftSilentInvariant
  ; WeakOneStepResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; targetTailChanges
  )
open import proof.ReductionProperties using
  (applyTyVars)


record WeakOneStepStoreLineage
    {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (result : WeakOneStepResult ρ M N′ A B χ) : Set₁ where
  constructor weak-step-store-lineage
  field
    lineageStore :
      StoreImp
        (resultCtx result)
        (resultLeftCtx result)
        (resultRightCtx result)

    lineageEmbedding :
      RelStoreEmbeddingⁱ
        (applyTyVars (sourceChanges result))
        (applyTyVars (χ ∷ targetTailChanges result))
        ρ lineageStore

    lineagePrefix :
      StoreImpPrefix lineageStore (resultStore result)

open WeakOneStepStoreLineage public


LineageAwareLeftSilentStoreCorrespondsTransportᵀ : Set₁
LineageAwareLeftSilentStoreCorrespondsTransportᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ : Ty}
    {α β : TyVar} {X X′ : Ty}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  WeakOneStepStoreLineage inner →
  StoreCorresponds ρ₀ α X β X′ pX →
  ∃[ pX′ ]
    StoreCorresponds
      (resultStore inner)
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyTyVars (targetTailChanges inner) β)
      (applyTys (targetTailChanges inner) X′)
      pX′
