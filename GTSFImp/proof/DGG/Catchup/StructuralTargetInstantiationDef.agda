module proof.DGG.Catchup.StructuralTargetInstantiationDef where

-- File Charter:
--   * Records target-only normalization of a typed instantiation spine.
--   * Separates the structural trace and reduction from relation replay.

open import Types using (Ty; TyCtx)
open import CastTerms using (Term; Value)
open import Reduction using (StoreChanges; _—↠[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendDef


record StructuralTargetInstantiationPackage {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (V : Term Δᴿ)
    {B E : Ty Δᴿ} (spine : InstantiationSpine B E) : Set₁ where
  field
    Δᴿ′ : TyCtx
    χs : StoreChanges Δᴿ Δᴿ′
    Δ′ : TyCtx
    W′ : CTI2.World Δᴸ Δᴿ′ Δ′
    structural-ext : StructuralWorldExtendᴿ χs W W′
    final : Term Δᴿ′
    final-value : Value final
    post-reduction : applyInstantiationSpine V spine —↠[ χs ] final
