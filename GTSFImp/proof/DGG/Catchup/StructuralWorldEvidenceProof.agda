module proof.DGG.Catchup.StructuralWorldEvidenceProof where

-- File Charter:
--   * Transports wrapper contexts and source conversion typing along traces.
--   * Supplies shared endpoint evidence for structural relation replay.

open import Data.Maybe using (Maybe)
open import Data.Nat using (suc)

open import Types using (Ty; TyVar)
open import Conversion using (Conv↑; Conv↓)
open import Imprecision using (X⊑★)
open import Reduction using (StoreChanges)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralWorldExtendDef


mapCtxᴿ-sameCtx : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δᵖ Δ′ Δᵖ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δᵖ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δᵖ′}
    {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → (extᵖ : ECR.WorldExtendᴿ χs Wᵖ Wᵖ′)
  → CTI2.SameCtx γ γᵖ
  → CTI2.SameCtx (ECR.mapCtxᴿ ext γ) (ECR.mapCtxᴿ extᵖ γᵖ)
mapCtxᴿ-sameCtx ext extᵖ CTI2.same-[] = CTI2.same-[]
mapCtxᴿ-sameCtx ext extᵖ (CTI2.same-∷ sc) =
  CTI2.same-∷ (mapCtxᴿ-sameCtx ext extᵖ sc)


mapCtxᴿ-liftCtxᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft X⊑★ W)}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → (extᴸ : ECR.WorldExtendᴿ χs
      (CTI2.liftWorldLeft X⊑★ W)
      (CTI2.liftWorldLeft X⊑★ W′))
  → CTI2.LiftCtxᴸ X⊑★ γ γᴸ
  → CTI2.LiftCtxᴸ X⊑★
      (ECR.mapCtxᴿ ext γ) (ECR.mapCtxᴿ extᴸ γᴸ)
mapCtxᴿ-liftCtxᴸ ext extᴸ CTI2.liftᴸ-[] = CTI2.liftᴸ-[]
mapCtxᴿ-liftCtxᴸ ext extᴸ (CTI2.liftᴸ-∷ liftγ) =
  CTI2.liftᴸ-∷ (mapCtxᴿ-liftCtxᴸ ext extᴸ liftγ)


mapCtxᴿ-smartLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ Δᵐ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    {Wᵐ′ : CTI2.World (suc Δᴸ) Δᴿ′ Δᵐ′}
    {γ : CTI2.CtxImp W} {γᵐ : CTI2.CtxImp Wᵐ}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → (extᵐ : ECR.WorldExtendᴿ χs Wᵐ Wᵐ′)
  → CTI2.SmartLiftCtxᴸ γ γᵐ
  → CTI2.SmartLiftCtxᴸ
      (ECR.mapCtxᴿ ext γ) (ECR.mapCtxᴿ extᵐ γᵐ)
mapCtxᴿ-smartLiftCtxᴸ ext extᵐ CTI2.smart-lift-[] =
  CTI2.smart-lift-[]
mapCtxᴿ-smartLiftCtxᴸ ext extᵐ (CTI2.smart-lift-∷ liftγ) =
  CTI2.smart-lift-∷ (mapCtxᴿ-smartLiftCtxᴸ ext extᵐ liftγ)


structural-source-reveal : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X? : Maybe (TyVar Δᴸ)} {A B : Ty Δᴸ}
    {c : Conv↑ Δᴸ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTI2.sourceStoreʷ W CTI2.⊢↑[ X? ] c
  → CTI2.sourceStoreʷ W′ CTI2.⊢↑[ X? ] c
structural-source-reveal structural-[] c⊢ = c⊢
structural-source-reveal (structural-keep plan) c⊢ =
  structural-source-reveal plan c⊢
structural-source-reveal (structural-bind ins follows plan) c⊢ =
  structural-source-reveal plan (TE.source-reveal-insert ins c⊢)


structural-source-conceal : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X? : Maybe (TyVar Δᴸ)} {A B : Ty Δᴸ}
    {c : Conv↓ Δᴸ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTI2.sourceStoreʷ W CTI2.⊢↓[ X? ] c
  → CTI2.sourceStoreʷ W′ CTI2.⊢↓[ X? ] c
structural-source-conceal structural-[] c⊢ = c⊢
structural-source-conceal (structural-keep plan) c⊢ =
  structural-source-conceal plan c⊢
structural-source-conceal (structural-bind ins follows plan) c⊢ =
  structural-source-conceal plan (TE.source-conceal-insert ins c⊢)
