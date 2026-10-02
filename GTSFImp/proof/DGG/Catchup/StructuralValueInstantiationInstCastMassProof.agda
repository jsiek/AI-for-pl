module
  proof.DGG.Catchup.StructuralValueInstantiationInstCastMassProof where

-- File Charter:
--   * Proves primary cast-mass descent for allocating `safe-inst`.
--   * Uses the concrete type app, reveal, residual cast, and mapped spine.

import Data.Fin as Fin
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using
  (+-monoˡ-<; +-monoʳ-<; n<1+n; ≤-<-trans)
open import Relation.Binary.PropositionalEquality using
  (_≢_; refl; sym; trans)

open import Types
open import Consistency using
  (Env∼; instᵐ; inst_; ↑ᶜ_; close-instᶜ)
open import Conversion using (〖_,_↑_〗)
import CastTerms as CT
open import Reduction using (bind; applyBody)
open import proof.TypeInTermSubst using
  (renameᵗ-wk-eq; renameᵗᵐ-preserves-Value)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
open import proof.Consistency using (castSize; castSize-close-inst-≤)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationCastMassDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationValueCastMassProof
open import
  proof.DGG.Catchup.StructuralValueInstantiationSpineCastMassProof


inst-primary-decreases : ∀ {Δ} {A : Ty (suc Δ)} {B E : Ty Δ}
    {μ : Env∼ Δ} {V} {c : instᵐ μ Consistency.⊢ A ∼ ⇑ᵗ B}
    ⦃ Anv : NonVar A ⦄ ⦃ z∈A : Fin.zero ∈ᵗ A ⦄
    (vV : CT.Value V) (B≠★ : B ≢ ★)
    (spine : InstantiationSpine B E)
  → pendingCastMass (renameᵗᵐ-preserves-Value Consistency.wk↪ᵗ vV)
      (name-type-app-frame (applyBody (bind ★) A) Fin.zero
          refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero A) ▻ⁱ
        reveal-frame (〖 Fin.zero , ★ ↑ A 〗) ▻ⁱ
        type-transport-frame
          (trans (replace-zero-open A ★)
            (sym (renameᵗ-wk-eq (A [ ★ ]ᵗ)))) ▻ⁱ
        cast-frame (↑ᶜ (close-instᶜ c)) ▻ⁱ
        type-transport-frame (renameᵗ-wk-eq B) ▻ⁱ
        mapInstantiationSpine (bind ★) spine) <
      pendingCastMass vV (cast-frame ((inst c) B≠★) ▻ⁱ spine)
inst-primary-decreases {c = c} vV B≠★ spine
    rewrite value-cast-mass-rename Consistency.wk↪ᵗ vV
          | spine-cast-mass-map (bind ★) spine =
  +-monoʳ-< (valueCastMass vV)
    (+-monoˡ-< (spineCastMass spine)
      (≤-<-trans (castSize-close-inst-≤ c)
        (n<1+n (castSize c))))
