module
  proof.Store.Lineage.NuImprecisionStoreCorrespondsLineageTransportProof
  where

-- File Charter:
--   * Proves correspondence transport from explicit weak-result lineage.
--   * Handles both stored and linked correspondences through ambient and
--     result allocation prefixes.
--   * Bridges the canonical store-change renaming to `applyTys` endpoints.
--   * Contains no simulation, catch-up, silent-result premise, theorem-
--     fragment alias, or lineage construction.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import ImprecisionComposition using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using
  (sym; trans)

open import NuReduction using
  ( StoreChanges
  ; applyTys
  ; bind
  ; keep
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreCorresponds
  ; StoreImp
  ; correspondence-linked
  ; correspondence-stored
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  )
open import Types using
  (Ty; TyVar; renameᵗ; ⇑ᵗ)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingProof using
  (rel-store-embedding-correspondenceⁱ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  )
open import NuTerms using (Term)
open import Types using (Ty; TyCtx; TyVar)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; resultStore
  ; sourceChanges
  ; targetTailChanges
  )
open import proof.Core.Properties.ReductionProperties using
  (applyTyVars; applyTys-rename-applyTyVars)


store-corresponds-weakenⁱ :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {α β : TyVar} {A B : Ty} {p} →
  StoreImpPrefix ρ₀ ρ⁺ →
  StoreCorresponds ρ₀ α A β B p →
  StoreCorresponds ρ⁺ α A β B p
store-corresponds-weakenⁱ prefix-reflⁱ corr = corr
store-corresponds-weakenⁱ (prefix-∷ⁱ prefix) corr
    with store-corresponds-weakenⁱ prefix corr
store-corresponds-weakenⁱ (prefix-∷ⁱ prefix) corr
    | correspondence-stored member =
  correspondence-stored (there member)
store-corresponds-weakenⁱ (prefix-∷ⁱ prefix) corr
    | correspondence-linked member =
  correspondence-linked (there member)


store-corresponds-reindexⁱ :
  ∀ {Φ Δᴸ Δᴿ} {ρ : StoreImp Φ Δᴸ Δᴿ}
    {α α′ β β′ : TyVar} {A A′ B B′ : Ty} {p} →
  α ≡ α′ →
  A ≡ A′ →
  β ≡ β′ →
  B ≡ B′ →
  StoreCorresponds ρ α A β B p →
  ∃[ p′ ]
    StoreCorresponds ρ α′ A′ β′ B′ p′
    × (⌊ p′ ⌋ ≡ ⌊ p ⌋)
store-corresponds-reindexⁱ refl refl refl refl corr =
  _ , corr , refl


store-corresponds-lineage-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ : Ty}
    {α β : TyVar} {X X′ : Ty}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
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
    × (⌊ pX′ ⌋ ≡ ⌊ pX ⌋)
store-corresponds-lineage-transportᵀ
    prefix inner lineage corr
    with store-corresponds-weakenⁱ prefix corr
store-corresponds-lineage-transportᵀ
    prefix inner lineage corr | corr⁺
    with rel-store-embedding-correspondenceⁱ
      (lineageEmbedding lineage) corr⁺
store-corresponds-lineage-transportᵀ
    prefix inner lineage corr | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , p₁-shape , corr₁
    with store-corresponds-reindexⁱ
      eqα
      (trans eqX
        (sym (applyTys-rename-applyTyVars
          (sourceChanges inner) _)))
      eqβ
      (trans eqX′
        (sym (applyTys-rename-applyTyVars
          (targetTailChanges inner) _)))
      corr₁
store-corresponds-lineage-transportᵀ
    prefix inner lineage corr | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , p₁-shape , corr₁
    | p₂ , corr₂ , p₂-shape =
  p₂ ,
  store-corresponds-weakenⁱ (lineagePrefix lineage) corr₂ ,
  trans p₂-shape p₁-shape
