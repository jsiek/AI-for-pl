module proof.DGG.Catchup.StructuralTargetInstStepProof where

-- File Charter:
--   * Builds the target-only β-inst trace under a pending spine.
--   * Exposes the strictly smaller residual-cast child state.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using
  (_≢_; refl; sym; trans)

open import Types using
  (Ty; NonVar; _∈ᵗ_; ＇_; ★; _[_]ᵗ; ⇑ᵗ)
open import Consistency using
  (Env∼; _⊢_∼_; instᵐ; inst_; ↑ᶜ_; close-instᶜ)
open import CastTerms using
  (Term; Value; _⟨_⟩; _⦂∀_[_]; _↑_; ⇑ᵗᵐ)
open import Conversion using (〖_,_↑_〗)
open import Reduction using (bind; applyBody; β-inst)
open import proof.TypeInTermSubst using (renameᵗ-wk-eq)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
import proof.DGG.CtxImp as CTI2
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationReductionProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetInstantiationProof


structural-target-inst-step : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴿ)} {B E : Ty Δᴿ}
    {μ : Env∼ Δᴿ} {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
    {V : Term Δᴿ} (vV : Value V) (B≠★ : B ≢ ★)
    (spine : InstantiationSpine B E)
  → StructuralTargetInstantiationPackage
      (CTI2.rightOnlyWorld W ★) (⇑ᵗᵐ V)
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
  → StructuralTargetInstantiationPackage W V
      (cast-frame ((inst c) B≠★) ▻ⁱ spine)
structural-target-inst-step {W = W} vV B≠★ spine child =
  structural-target-bind-step
    (TE.rightBindTargetInsert {W = W} {B = ★}) refl
    (lift-instantiation-spine-bind (β-inst vV B≠★) spine)
    child
