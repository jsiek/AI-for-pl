module proof.DGG.Catchup.StructuralTargetGenStepProof where

-- File Charter:
--   * Builds the target-only β-gen trace under a pending spine.
--   * Exposes the strictly smaller cast-mass child state.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types using
  (Ty; TyVar; NonVar; _∈ᵗ_; ＇_; ★; _[_]ᵗ; ⇑ᵗ)
open import Consistency using (Env∼; _⊢_∼_; genᵐ; gen_)
open import CastTerms using
  (Term; Value; GenSafe; _⟨_⟩; _⦂∀_[_]; _↑_; ⇑ᵗᵐ)
open import Conversion using (〖_,_↑_〗)
open import Reduction using (bind; β-gen)
open import proof.TypeInTermSubst using
  (renameᵗᵐ-preserves-Value)
open import proof.TypeSafety.Preservation using (replace-zero-open)
import proof.DGG.CtxImp as CTI2
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationReductionProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetInstantiationProof


structural-target-gen-step : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴿ} {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {μ : Env∼ Δᴿ} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
    ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : Fin.zero ∈ᵗ B ⦄
    {V : Term Δᴿ} {X : TyVar Δᴿ}
    (fresh : CTI2.RightBindFresh W (＇ X))
    (vV : Value V) (A≠★ : A ≢ ★) (safe : GenSafe c)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → StructuralTargetInstantiationPackage
      (CTI2.rightOnlyWorld W (＇ X) fresh)
      (⇑ᵗᵐ V)
      (cast-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine)
  → StructuralTargetInstantiationPackage W
      (V ⟨ (gen c) A≠★ ⟩)
      (name-type-app-frame B X refl refl ▻ⁱ spine)
structural-target-gen-step {W = W} {X = X}
    fresh vV A≠★ safe spine child =
  structural-target-bind-step
    (TE.rightBindTargetInsert {W = W} {B = ＇ X} fresh) refl
    (lift-instantiation-spine-bind (β-gen vV A≠★ safe) spine)
    child
