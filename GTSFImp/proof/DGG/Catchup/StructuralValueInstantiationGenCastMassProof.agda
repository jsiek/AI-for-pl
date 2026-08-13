module
  proof.DGG.Catchup.StructuralValueInstantiationGenCastMassProof where

-- File Charter:
--   * Proves primary cast-mass descent for the allocating `gen` step.
--   * Uses the concrete generated reveal and allocated pending spine.

import Data.Fin as Fin
open import Data.Nat using (_<_; _+_; suc)
open import Data.Nat.Properties using (+-assoc; n<1+n)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; subst)

open import Types
open import Consistency using (Env∼; genᵐ)
open import Conversion using (〖_,_↑_〗)
import CastTerms as CT
open import Reduction using (bind)
open import proof.Consistency using (castSize)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
open import proof.TypeSafety.Preservation using (replace-zero-open)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationCastMassDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationCastMassProof
open import
  proof.DGG.Catchup.StructuralValueInstantiationValueCastMassProof
open import
  proof.DGG.Catchup.StructuralValueInstantiationSpineCastMassProof


gen-primary-decreases : ∀ {Δ} {A : Ty Δ} {B : Ty (suc Δ)}
    {E : Ty Δ} {μ : Env∼ Δ} {V} {X : TyVar Δ}
    {c : genᵐ μ Consistency.⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    {A≠★ : A ≢ ★} (vV : CT.Value V) (safe : CT.GenSafe c)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → pendingCastMass (renameᵗᵐ-preserves-Value Consistency.wk↪ᵗ vV)
      (cast-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine) <
      pendingCastMass (vV CT.《 CT.genᵥ A≠★ safe 》)
        (name-type-app-frame B X refl refl ▻ⁱ spine)
gen-primary-decreases {X = X} {c = c} {A≠★ = A≠★} vV safe spine
    rewrite value-cast-mass-rename Consistency.wk↪ᵗ vV
          | spine-cast-mass-map (bind (＇ X)) spine
          | gen-value-cast-mass-gap {A≠★ = A≠★} vV safe =
  subst (λ n → n < suc ((valueCastMass vV + castSize c) +
      spineCastMass spine))
    (+-assoc (valueCastMass vV) (castSize c) (spineCastMass spine))
    (n<1+n _)
