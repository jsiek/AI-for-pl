module proof.DGG.Catchup.StructuralTargetConversionStepProof where

-- File Charter:
--   * Builds target β-reveal-∀ and β-conceal-∀ trace steps.
--   * Records their fresh bind and explicit inner conversion frames.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (Ty; TyVar; ＇_; _[_]ᵗ; ⇑ᵗ)
open import Conversion using
  (Conv↑; Conv↓; `∀↑_; `∀↓_; 〖_,_↑_〗)
open import CastTerms using
  (Term; Value; _⦂∀_[_]; _↑_; _↓_; ⇑ᵗᵐ)
open import Reduction using
  (bind; applyBody; β-reveal-∀; β-conceal-∀)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
import proof.DGG.CtxImp as CTI2
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationReductionProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetInstantiationProof


structural-target-reveal-step : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {c : Conv↑ (suc Δᴿ) C B}
    {V : Term Δᴿ} {X : TyVar Δᴿ}
    (vV : Value V) (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → StructuralTargetInstantiationPackage
      (CTI2.rightOnlyWorld W (＇ X)) (⇑ᵗᵐ V)
      (name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
          refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        reveal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine)
  → StructuralTargetInstantiationPackage W (V ↑ `∀↑ c)
      (name-type-app-frame B X refl refl ▻ⁱ spine)
structural-target-reveal-step {W = W} {X = X} vV spine child =
  structural-target-bind-step
    (TE.rightBindTargetInsert {W = W} {B = ＇ X}) refl
    (lift-instantiation-spine-bind (β-reveal-∀ vV) spine) child


structural-target-conceal-step : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {c : Conv↓ (suc Δᴿ) C B}
    {V : Term Δᴿ} {X : TyVar Δᴿ}
    (vV : Value V) (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → StructuralTargetInstantiationPackage
      (CTI2.rightOnlyWorld W (＇ X)) (⇑ᵗᵐ V)
      (name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
          refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        conceal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine)
  → StructuralTargetInstantiationPackage W (V ↓ `∀↓ c)
      (name-type-app-frame B X refl refl ▻ⁱ spine)
structural-target-conceal-step {W = W} {X = X} vV spine child =
  structural-target-bind-step
    (TE.rightBindTargetInsert {W = W} {B = ＇ X}) refl
    (lift-instantiation-spine-bind (β-conceal-∀ vV) spine) child
