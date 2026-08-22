module proof.DGG.Catchup.StructuralTargetAllStepProof where

-- File Charter:
--   * Builds the target-only beta-all trace under a pending spine.
--   * Exposes the strictly smaller opened-cast child state.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (Ty; TyVar; ＇_; _[_]ᵗ)
open import Consistency using (Env∼; extᵐ; _⊢_∼_; ∀ᶜ_; _[_]ᶜ)
open import CastTerms using (Term; Value; _⟨_⟩)
open import Reduction using (keep; pure-step; β-∀)
import proof.DGG.CtxImp as CTI2
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationReductionProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetInstantiationProof


structural-target-all-step : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {μ : Env∼ Δᴿ} {d : extᵐ μ ⊢ A ∼ B}
    {V : Term Δᴿ} {X : TyVar Δᴿ}
    (vV : Value V)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → StructuralTargetInstantiationPackage W V
      (name-type-app-frame A X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine)
  → StructuralTargetInstantiationPackage W (V ⟨ ∀ᶜ d ⟩)
      (name-type-app-frame B X refl refl ▻ⁱ spine)
structural-target-all-step vV spine child =
  structural-target-keep-step
    (lift-instantiation-spine-keep
      (pure-step (β-∀ vV refl)) spine)
    child
