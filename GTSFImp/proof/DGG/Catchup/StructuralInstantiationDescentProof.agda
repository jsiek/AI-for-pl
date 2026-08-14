module proof.DGG.Catchup.StructuralInstantiationDescentProof where

-- File Charter:
--   * Builds the zero-spine structural descent package.
--   * Erases structural traces to the public instantiation package.

open import Relation.Binary.PropositionalEquality using (sym)
  renaming (subst to subst≡)

open import Types using (Ty)
open import CastTerms using (Term; Value)
open import Reduction using ([]; ↠-refl)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.InstInversionDef using
  (InstSpineDescentPackage)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetInstantiationProof
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Catchup.InstInversionDef using
  (StructuralValueInstantiationᵀ)
open import proof.DGG.Inversion.SpineValueProof using
  (rename-all-value-view)
open import proof.TypeInTermSubst using
  (renameᵗᵐ-preserves-Value)
open import Consistency using (wk↪ᵗ)


structural-descent-zero : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → Value V
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ q
  → StructuralInstantiationDescentPackage W γ M V []ⁱ q
structural-descent-zero {W = W} {γ = γ} vV rel = record
  { target-descent = structural-target-zero vV
  ; final-relation = subst≡
      (λ γ′ → W CTI2.∣ γ′ ⊢² _ ⊑ _ ∶ _)
      (sym (ECR.mapCtxᴿ-same γ)) rel
  }


erase-structural-descent : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ} {A : Ty Δᴸ} {B E : Ty Δᴿ}
    {spine : InstantiationSpine B E}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → StructuralInstantiationDescentPackage W γ M V spine q
  → InstSpineDescentPackage W γ M
      (applyInstantiationSpine V spine) q
erase-structural-descent pkg = record
  { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ target
  ; χs = StructuralTargetInstantiationPackage.χs target
  ; Δ′ = StructuralTargetInstantiationPackage.Δ′ target
  ; W′ = StructuralTargetInstantiationPackage.W′ target
  ; ext = structural-world-extendᴿ
      (StructuralTargetInstantiationPackage.structural-ext target)
  ; final = StructuralTargetInstantiationPackage.final target
  ; final-value = StructuralTargetInstantiationPackage.final-value target
  ; post-reduction = StructuralTargetInstantiationPackage.post-reduction target
  ; final-relation =
      StructuralInstantiationDescentPackage.final-relation pkg
  }
  where
  target = StructuralInstantiationDescentPackage.target-descent pkg


structural-name→value-instantiation :
  StructuralNameInstantiationᵀ
  → StructuralValueInstantiationᵀ
structural-name→value-instantiation worker rel vM vV view =
  erase-structural-descent
    (worker rel vM (renameᵗᵐ-preserves-Value wk↪ᵗ vV)
      (rename-all-value-view wk↪ᵗ view) []ⁱ)
