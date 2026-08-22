module proof.DGG.Catchup.StructuralInstDescentProof where

-- File Charter:
--   * Rebuilds relational structural descent across target β-inst.
--   * Consumes the strictly smaller residual-cast child package.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans)

open import Types using
  (Ty; NonVar; _∈ᵗ_; ＇_; ★; _[_]ᵗ; ⇑ᵗ)
open import Consistency using
  (Env∼; _↪ᵗ_; wk↪ᵗ; _⊢_∼_; instᵐ; inst_; ↑ᶜ_; close-instᶜ)
open import CastTerms using
  (Term; Value; _⟨_⟩; _⦂∀_[_]; _↑_; ⇑ᵗᵐ)
open import Conversion using (〖_,_↑_〗)
open import Reduction using
  (bind; applyBody; applyStores; _∷_; []; β-inst)
open import proof.TypeInTermSubst using (renameᵗ-wk-eq)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
import proof.DGG.CtxImp as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationReductionProof
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Catchup.StructuralInstantiationDescentProof


structural-inst-descent : ∀ {Δᴸ Δᴿ Δ Δ₁}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {L : Ty Δᴸ} {A : Ty (suc Δᴿ)} {B E : Ty Δᴿ}
    {π : Δ ↪ᵗ Δ₁}
    {μ : Env∼ Δᴿ} {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
    {q : L CTI2.⊑ᵂ⟨ W ⟩ E}
    (vV : Value V) (B≠★ : B ≢ ★)
    (spine : InstantiationSpine B E)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTI2.targetStoreʷ W₁ ≡
      applyStores (bind ★ ∷ []) (CTI2.targetStoreʷ W))
  → let ext = target-insert-bind-world-extendᴿ ins follows
     in StructuralInstantiationDescentPackage
          W₁
          (ECR.mapCtxᴿ ext γ) M (⇑ᵗᵐ V)
          (name-type-app-frame (applyBody (bind ★) A) Fin.zero
              refl refl ▻ⁱ
            type-transport-frame (applyBody-open-zero A) ▻ⁱ
            reveal-frame (〖 Fin.zero , ★ ↑ A 〗) ▻ⁱ
            type-transport-frame
              (trans (replace-zero-open A ★)
                (sym (renameᵗ-wk-eq (A [ ★ ]ᵗ)))) ▻ⁱ
            cast-frame (↑ᶜ (close-instᶜ c)) ▻ⁱ
            type-transport-frame (renameᵗ-wk-eq B) ▻ⁱ
            mapInstantiationSpine (bind ★) spine)
          (ECR.transport⊑ᵂ ext q)
  → StructuralInstantiationDescentPackage W γ M V
      (cast-frame ((inst c) B≠★) ▻ⁱ spine) q
structural-inst-descent {W = W} vV B≠★ spine ins follows child =
  structural-descent-bind-step
    ins follows
    (lift-instantiation-spine-bind (β-inst vV B≠★) spine)
    child
