module proof.DGG.Catchup.StructuralTermProvenanceDef where

-- File Charter:
--   * Records relation-indexed target-insertion provenance along a complete
--     structural right-world extension.
--   * Keeps each transported term-imprecision derivation adjacent to the
--     insertion evidence that produced it.
--   * Contains no provenance synthesis or replay proofs.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import CastTerms using (Term)
open import Reduction using (StoreChanges; []; _∷_; bind; applyStores)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralWorldExtendDef using
  (StructuralWorldExtendᴿ; structural-[]; structural-keep;
   structural-bind)


data StructuralTermProvenance {Δᴸ} :
    ∀ {Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {W : CTX.World Δᴸ Δᴿ Δ}
      {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
      {γ : CTX.CtxImp W}
      {M : Term Δᴸ} {N : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {p : A CTX.⊑ᵂ⟨ W ⟩ B}
    → (plan : StructuralWorldExtendᴿ χs W W′)
    → (rel : W CTI2.∣ γ ⊢² M ⊑ N ∶ p)
    → Set₁ where

  term-provenance-[] : ∀ {Δᴿ Δ}
      {W : CTX.World Δᴸ Δᴿ Δ}
      {γ : CTX.CtxImp W}
      {M : Term Δᴸ} {N : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {p : A CTX.⊑ᵂ⟨ W ⟩ B}
      {rel : W CTI2.∣ γ ⊢² M ⊑ N ∶ p}
    → StructuralTermProvenance structural-[] rel

  term-provenance-keep : ∀ {Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {W : CTX.World Δᴸ Δᴿ Δ}
      {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
      {γ : CTX.CtxImp W}
      {M : Term Δᴸ} {N : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {p : A CTX.⊑ᵂ⟨ W ⟩ B}
      {plan : StructuralWorldExtendᴿ χs W W′}
      {rel : W CTI2.∣ γ ⊢² M ⊑ N ∶ p}
    → StructuralTermProvenance plan rel
    → StructuralTermProvenance (structural-keep plan) rel

  term-provenance-bind : ∀ {Δᴿ Δᴿ′ Δ Δ₁ Δ′}
      {R : Ty Δᴿ} {π : Δ ↪ᵗ Δ₁}
      {χs : StoreChanges (suc Δᴿ) Δᴿ′}
      {W : CTX.World Δᴸ Δᴿ Δ}
      {W₁ : CTX.World Δᴸ (suc Δᴿ) Δ₁}
      {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
      {γ : CTX.CtxImp W}
      {M : Term Δᴸ} {N : Term Δᴿ}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {p : A CTX.⊑ᵂ⟨ W ⟩ B}
      {ins : TE.TargetInsert wk↪ᵗ π W W₁}
      {follows : CTX.targetStoreʷ W₁ ≡
        applyStores (bind R ∷ []) (CTX.targetStoreʷ W)}
      {plan : StructuralWorldExtendᴿ χs W₁ W′}
      {rel : W CTI2.∣ γ ⊢² M ⊑ N ∶ p}
    → (provenance : TE.TargetInsertProvenance W₁ ins rel)
    → StructuralTermProvenance plan
        (TE.⊢²-target-insert W₁ ins rel provenance)
    → StructuralTermProvenance
        (structural-bind ins follows plan) rel
