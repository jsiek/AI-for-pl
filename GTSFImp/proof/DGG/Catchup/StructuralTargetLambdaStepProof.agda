module proof.DGG.Catchup.StructuralTargetLambdaStepProof where

-- File Charter:
--   * Builds the target-only β-Λ trace step under a pending spine.
--   * Exposes the value-anchored generated-reveal helper used by NS-4.
--   * Records the fresh right bind and the opened-type transport.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (Ty; TyVar; ＇_; _[_]ᵗ; ⇑ᵗ)
open import CastTerms using (Term; Value; Λ_; _⦂∀_[_]; _↑_)
open import Conversion using (〖_,_↑_〗)
open import Reduction using (bind; β-Λ)
open import proof.TypeSafety.Preservation using (replace-zero-open)
import proof.DGG.CtxImp as CTI2
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationReductionProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetInstantiationProof


structural-target-Λ-step : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴿ} {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {V : Term (suc Δᴿ)}
    (fresh : CTI2.RightBindFresh W (＇ X))
    (vV : Value V)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → StructuralTargetInstantiationPackage
      (CTI2.rightOnlyWorld W (＇ X) fresh)
      (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)
      (type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine)
  → StructuralTargetInstantiationPackage W (Λ V)
      (name-type-app-frame B X refl refl ▻ⁱ spine)
structural-target-Λ-step {W = W} {X = X} fresh vV spine child =
  structural-target-bind-step
    (TE.rightBindTargetInsert {W = W} {B = ＇ X} fresh) refl
    (lift-instantiation-spine-bind (β-Λ vV) spine) child


structural-target-Λ-value-step : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴿ} {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {V : Term (suc Δᴿ)}
    (fresh : CTI2.RightBindFresh W (＇ X))
    (vV : Value V)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → StructuralTargetInstantiationPackage
      (CTI2.rightOnlyWorld W (＇ X) fresh)
      V
      (reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine)
  → StructuralTargetInstantiationPackage W (Λ V)
      (name-type-app-frame B X refl refl ▻ⁱ spine)
structural-target-Λ-value-step fresh vV spine child =
  structural-target-Λ-step fresh vV spine
    (structural-target-frame-peel child)
