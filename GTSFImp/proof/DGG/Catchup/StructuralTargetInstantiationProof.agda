module proof.DGG.Catchup.StructuralTargetInstantiationProof where

-- File Charter:
--   * Constructs target-only normalization for an empty pending spine.

open import Types using (Ty)
open import CastTerms using (Term; Value)
open import Reduction using ([]; ↠-refl)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralTargetInstantiationDef


structural-target-zero : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {V : Term Δᴿ} {B : Ty Δᴿ}
  → Value V
  → StructuralTargetInstantiationPackage W V {B = B} []ⁱ
structural-target-zero {W = W} vV = record
  { Δᴿ′ = _
  ; χs = []
  ; Δ′ = _
  ; W′ = W
  ; structural-ext = structural-[]
  ; final = _
  ; final-value = vV
  ; post-reduction = ↠-refl
  }
