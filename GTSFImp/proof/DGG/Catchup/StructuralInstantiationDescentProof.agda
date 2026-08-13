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
open import proof.DGG.Catchup.StructuralInstantiationDescentDef


structural-descent-zero : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → Value V
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ q
  → StructuralInstantiationDescentPackage W γ M V []ⁱ q
structural-descent-zero {W = W} {γ = γ} vV rel = record
  { Δᴿ′ = _
  ; χs = []
  ; Δ′ = _
  ; W′ = W
  ; structural-ext = structural-[]
  ; final = _
  ; final-value = vV
  ; post-reduction = ↠-refl
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
  { Δᴿ′ = StructuralInstantiationDescentPackage.Δᴿ′ pkg
  ; χs = StructuralInstantiationDescentPackage.χs pkg
  ; Δ′ = StructuralInstantiationDescentPackage.Δ′ pkg
  ; W′ = StructuralInstantiationDescentPackage.W′ pkg
  ; ext = structural-world-extendᴿ
      (StructuralInstantiationDescentPackage.structural-ext pkg)
  ; final = StructuralInstantiationDescentPackage.final pkg
  ; final-value = StructuralInstantiationDescentPackage.final-value pkg
  ; post-reduction =
      StructuralInstantiationDescentPackage.post-reduction pkg
  ; final-relation =
      StructuralInstantiationDescentPackage.final-relation pkg
  }
