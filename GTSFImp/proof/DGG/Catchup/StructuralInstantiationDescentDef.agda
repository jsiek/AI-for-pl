module proof.DGG.Catchup.StructuralInstantiationDescentDef where

-- File Charter:
--   * Records target-spine descent with a structural world-extension trace.
--   * Retains insertion history until source wrappers have been rebuilt.

open import Types using (Ty; TyCtx)
open import CastTerms using (Term; Value)
open import Reduction using (StoreChanges; _—↠[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef


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
