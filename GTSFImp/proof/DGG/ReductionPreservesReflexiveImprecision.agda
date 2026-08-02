module proof.DGG.ReductionPreservesReflexiveImprecision where

-- File Charter:
--   * Proves the DGG warm-up that reflexive cast-term imprecision is
--     preserved by one store-changing reduction step.
--   * Uses the two-renaming cast-term imprecision relation with identity
--     embeddings on both reducts.
--   * Depends on type preservation, type-variable renaming for typing, and
--     the reflexivity infrastructure for cast-term imprecision.

open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using ()
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym)
  renaming (subst to subst≡)

open import Types
open import TyStore using (TyStore; store-empty; store-lift; store-bind; _∋_⦂_)
open import Consistency using (id↪ᵗ; toRenameᵗ)
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
open import Reduction
  using (StoreChange; _—→[_]_; applyStore; applyTy)
open import proof.TypeSafety.Preservation using (preservation)
open import proof.TypeInTermSubst using
  (StoreRename; toRename-id-eq; renameᵗ-pointwise-id;
   typing-renameᵗ)
open import proof.ImprecisionConsistency using (refl⊑)
import proof.DGG.CastTermImprecision as CTI

open CTI using
  (categoriesⁱ; impEnvⁱ; reflStoreImp; reflCtx; _∣_∣_∣_⊢ᶜ_⊑_∶_)

------------------------------------------------------------------------
-- Identity embedding facts
------------------------------------------------------------------------

renameᵗ-toRename-id : ∀ {Δ} (A : Ty Δ)
  → renameᵗ (toRenameᵗ id↪ᵗ) A ≡ A
renameᵗ-toRename-id A =
  renameᵗ-pointwise-id (toRenameᵗ id↪ᵗ) A toRename-id-eq

StoreRename-toRename-id : ∀ {Δ} {Σ : TyStore Δ}
  → StoreRename (toRenameᵗ id↪ᵗ) Σ Σ
StoreRename-toRename-id {Σ = Σ} {X = X} {A = A} X∈ =
  subst≡
    (λ Y → Σ ∋ Y ⦂ renameᵗ (toRenameᵗ id↪ᵗ) A)
    (sym (toRename-id-eq X))
    (subst≡ (λ B → Σ ∋ X ⦂ B)
      (sym (renameᵗ-toRename-id A)) X∈)

id-image : ∀ {Δ} (X : TyVar Δ) → CTI.InImage id↪ᵗ X
id-image X = CTI.image X (toRename-id-eq X)

lift-id-image-category : ∀ {Δ category} {X : TyVar Δ}
  → CTI.ImageCategory id↪ᵗ id↪ᵗ X category
  → CTI.ImageCategory id↪ᵗ id↪ᵗ (Fin.suc X) category
lift-id-image-category (CTI.image-both _ _) =
  CTI.image-both (id-image (Fin.suc _)) (id-image (Fin.suc _))
lift-id-image-category (CTI.image-left-only _ not-right) =
  ⊥-elim (not-right (id-image _))
lift-id-image-category (CTI.image-right-only not-left _) =
  ⊥-elim (not-left (id-image _))

reflStoreImp-renamings-categorize : ∀ {Δ} (Σ : TyStore Δ)
  → CTI.RenamingsCategorize id↪ᵗ id↪ᵗ
      (categoriesⁱ (reflStoreImp Σ))
reflStoreImp-renamings-categorize store-empty ()
reflStoreImp-renamings-categorize (store-lift Σ) X
    with reflStoreImp Σ | reflStoreImp-renamings-categorize Σ
reflStoreImp-renamings-categorize (store-lift Σ) Fin.zero
    | CTI.stores μ Σᴸ Σᴿ categories | rec =
  CTI.image-both (id-image Fin.zero) (id-image Fin.zero)
reflStoreImp-renamings-categorize (store-lift Σ) (Fin.suc X)
    | CTI.stores μ Σᴸ Σᴿ categories | rec =
  lift-id-image-category (rec X)
reflStoreImp-renamings-categorize (store-bind Σ A) X
    with reflStoreImp Σ | reflStoreImp-renamings-categorize Σ
reflStoreImp-renamings-categorize (store-bind Σ A) Fin.zero
    | CTI.stores μ Σᴸ Σᴿ categories | rec =
  CTI.image-both (id-image Fin.zero) (id-image Fin.zero)
reflStoreImp-renamings-categorize (store-bind Σ A) (Fin.suc X)
    | CTI.stores μ Σᴸ Σᴿ categories | rec =
  lift-id-image-category (rec X)

------------------------------------------------------------------------
-- Reduction preserves reflexive imprecision
------------------------------------------------------------------------

reduction-preserves-reflᶜ : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {M : Term Δ} {N : Term Δ′} {A : Ty Δ}
    {χ : StoreChange Δ Δ′}
  → ⟨ Δ , Σ , [] ⟩ ⊢ M ⦂ A
  → M —→[ χ ] N
  → id↪ᵗ ∣ id↪ᵗ ∣ reflStoreImp (applyStore χ Σ)
      ∣ reflCtx (impEnvⁱ (reflStoreImp (applyStore χ Σ))) []
      ⊢ᶜ N ⊑ N ∶ refl⊑ (applyTy χ A)
reduction-preserves-reflᶜ {Σ = Σ} {N = N} {A = A} {χ = χ} M⊢ step =
  subst≡
    (λ B → id↪ᵗ ∣ id↪ᵗ ∣ reflStoreImp (applyStore χ Σ)
      ∣ reflCtx (impEnvⁱ (reflStoreImp (applyStore χ Σ))) []
      ⊢ᶜ N ⊑ N ∶ refl⊑ B)
    (renameᵗ-toRename-id (applyTy χ A))
    (CTI.rename⊑renameᶜ
      (reflStoreImp-renamings-categorize (applyStore χ Σ))
      (CTI.reflᶜ (typing-renameᵗ StoreRename-toRename-id
        (preservation M⊢ step))))
