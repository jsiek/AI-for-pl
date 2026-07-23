module
  proof.Left.SilentTransport.NuImprecisionLeftSilentStoreCorrespondsTransportProof
  where

-- File Charter:
--   * Proves correspondence transport from explicit weak-result lineage.
--   * Handles both stored and linked correspondences through ambient and
--     result allocation prefixes.
--   * Bridges the canonical store-change renaming to `applyTys` endpoints.
--   * Contains no simulation, catch-up, or lineage construction.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat using (suc)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (sym; trans)

open import NuReduction using
  ( StoreChanges
  ; applyTys
  ; bind
  ; keep
  )
open import NuTermImprecision using
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
  ( LineageAwareLeftSilentStoreCorrespondsTransportᵀ
  ; WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  (sourceChanges; targetTailChanges)
open import proof.Core.Properties.ReductionProperties using
  (applyTyVars)
open import proof.Core.Properties.TypeProperties using
  (renameᵗ-compose; renameᵗ-id)


applyTys-rename-applyTyVars :
  ∀ (changes : StoreChanges) (A : Ty) →
  applyTys changes A ≡ renameᵗ (applyTyVars changes) A
applyTys-rename-applyTyVars [] A = sym (renameᵗ-id A)
applyTys-rename-applyTyVars (keep ∷ changes) A =
  applyTys-rename-applyTyVars changes A
applyTys-rename-applyTyVars (bind B ∷ changes) A =
  trans (applyTys-rename-applyTyVars changes (⇑ᵗ A))
        (renameᵗ-compose suc (applyTyVars changes) A)


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
  ∃[ p′ ] StoreCorresponds ρ α′ A′ β′ B′ p′
store-corresponds-reindexⁱ refl refl refl refl corr = _ , corr


left-silent-store-corresponds-transport-proofᵀ :
  LineageAwareLeftSilentStoreCorrespondsTransportᵀ
left-silent-store-corresponds-transport-proofᵀ
    prefix inner silent lineage corr
    with store-corresponds-weakenⁱ prefix corr
left-silent-store-corresponds-transport-proofᵀ
    prefix inner silent lineage corr | corr⁺
    with rel-store-embedding-correspondenceⁱ
      (lineageEmbedding lineage) corr⁺
left-silent-store-corresponds-transport-proofᵀ
    prefix inner silent lineage corr | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , corr₁
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
left-silent-store-corresponds-transport-proofᵀ
    prefix inner silent lineage corr | corr⁺
    | α′ , X₁ , β′ , X₁′ , p₁ ,
      eqα , eqX , eqβ , eqX′ , corr₁
    | p₂ , corr₂ =
  p₂ , store-corresponds-weakenⁱ
    (lineagePrefix lineage) corr₂
