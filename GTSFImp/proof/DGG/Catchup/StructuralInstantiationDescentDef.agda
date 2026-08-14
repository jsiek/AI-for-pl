module proof.DGG.Catchup.StructuralInstantiationDescentDef where

-- File Charter:
--   * Records target-spine descent with a structural world-extension trace.
--   * Retains insertion history until source wrappers have been rebuilt.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (refl)
open import Types using (Ty; TyCtx; TyVar; ＇_; `∀; _[_]ᵗ)
open import CastTerms using (Term; Value)
open import Reduction using (StoreChanges; _—↠[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)


record StructuralInstantiationDescentPackage {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (γ : CTI2.CtxImp W)
    (M : Term Δᴸ) (V : Term Δᴿ) {A : Ty Δᴸ} {B E : Ty Δᴿ}
    (spine : InstantiationSpine B E)
    (q : A CTI2.⊑ᵂ⟨ W ⟩ E) : Set₁ where
  field
    target-descent : StructuralTargetInstantiationPackage W V spine
    final-relation :
      StructuralTargetInstantiationPackage.W′ target-descent CTI2.∣
        ECR.mapCtxᴿ (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext
            target-descent)) γ
        ⊢² M ⊑
          StructuralTargetInstantiationPackage.final target-descent ∶
          ECR.transport⊑ᵂ
            (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext
                target-descent)) q


StructuralNameInstantiationᵀ : Set₁
StructuralNameInstantiationᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → Value M
  → Value V
  → AllValueView V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → StructuralInstantiationDescentPackage W γ M V
      (name-type-app-frame B X refl refl ▻ⁱ spine) q
