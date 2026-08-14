module proof.DGG.Catchup.StructuralAllDescentProof where

-- File Charter:
--   * Rebuilds structural descent across a target universal cast.
--   * Consumes the strictly smaller opened-cast child package.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (refl; sym)
  renaming (subst to subst≡)

open import Types using (Ty; TyVar; ＇_; _[_]ᵗ)
open import Consistency using (Env∼; extᵐ; _⊢_∼_; ∀ᶜ_; _[_]ᶜ)
open import CastTerms using (Term; Value; _⟨_⟩)
open import Reduction using (keep)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetAllStepProof
open import proof.DGG.Catchup.StructuralInstantiationDescentDef


structural-all-descent : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {μ : Env∼ Δᴿ} {d : extᵐ μ ⊢ B ∼ C}
    {X : TyVar Δᴿ} {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
    (vV : Value V)
    (spine : InstantiationSpine (C [ ＇ X ]ᵗ) E)
  → StructuralInstantiationDescentPackage W γ M V
      (name-type-app-frame B X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine) q
  → StructuralInstantiationDescentPackage W γ M (V ⟨ ∀ᶜ d ⟩)
      (name-type-app-frame C X refl refl ▻ⁱ spine) q
structural-all-descent {W = W} {γ = γ} vV spine child = record
  { target-descent = target
  ; final-relation = subst≡
      (λ γ′ → _ CTI2.∣ γ′ ⊢² _ ⊑ _ ∶ _)
      (sym (mapCtxᴿ-structural-keep
        (StructuralTargetInstantiationPackage.structural-ext child-target)
        γ))
      (StructuralInstantiationDescentPackage.final-relation child)
  }
  where
  child-target =
    StructuralInstantiationDescentPackage.target-descent child
  target = structural-target-all-step vV spine child-target
