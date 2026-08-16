module proof.DGG.Catchup.StructuralWorldEvidenceProof where

-- File Charter:
--   * Transports wrapper contexts and conversion typing along traces.
--   * Supplies shared endpoint evidence for structural relation replay.

import Data.Fin as Fin
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
  renaming (subst to subst≡)

open import Types using (Ty; TyVar)
open import Consistency using (wk↪ᵗ; toRenameᵗ)
open import Conversion using (Conv↑; Conv↓; rename↑; rename↓)
open import Imprecision using (X⊑★)
open import Reduction using (StoreChanges)
open import proof.TypeInTermSubst using
  (StoreRename-suc-bind; toRename-wk-eq)
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


mapPivot-wk-eq : ∀ {Δ} (X? : Maybe (TyVar Δ))
  → TE.mapPivot Fin.suc X?
      ≡ TE.mapPivot (toRenameᵗ wk↪ᵗ) X?
mapPivot-wk-eq nothing = refl
mapPivot-wk-eq (just X) = cong just (sym (toRename-wk-eq X))


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


structural-target-reveal : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X? : Maybe (TyVar Δᴿ)} {A B : Ty Δᴿ}
    {c : Conv↑ Δᴿ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTI2.targetStoreʷ W CTI2.⊢↑[ X? ] c
  → CTI2.targetStoreʷ W′ CTI2.⊢↑[ mapPivotChanges χs X? ]
      mapRevealChanges χs c
structural-target-reveal structural-[] c⊢ = c⊢
structural-target-reveal (structural-keep plan) c⊢ =
  structural-target-reveal plan c⊢
structural-target-reveal {X? = X?} {c = c}
    (structural-bind {W₁ = W₁} ins follows plan) c⊢ =
  structural-target-reveal plan
    (subst≡
      (λ pivot → CTI2.targetStoreʷ W₁ CTI2.⊢↑[ pivot ]
        rename↑ Fin.suc c)
      (mapPivot-wk-eq X?)
      (subst≡
        (λ Σ → Σ CTI2.⊢↑[ TE.mapPivot Fin.suc X? ] rename↑ Fin.suc c)
        (sym follows)
        (TE.reveal-renameˣ StoreRename-suc-bind c⊢)))


structural-target-conceal : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X? : Maybe (TyVar Δᴿ)} {A B : Ty Δᴿ}
    {c : Conv↓ Δᴿ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTI2.targetStoreʷ W CTI2.⊢↓[ X? ] c
  → CTI2.targetStoreʷ W′ CTI2.⊢↓[ mapPivotChanges χs X? ]
      mapConcealChanges χs c
structural-target-conceal structural-[] c⊢ = c⊢
structural-target-conceal (structural-keep plan) c⊢ =
  structural-target-conceal plan c⊢
structural-target-conceal {X? = X?} {c = c}
    (structural-bind {W₁ = W₁} ins follows plan) c⊢ =
  structural-target-conceal plan
    (subst≡
      (λ pivot → CTI2.targetStoreʷ W₁ CTI2.⊢↓[ pivot ]
        rename↓ Fin.suc c)
      (mapPivot-wk-eq X?)
      (subst≡
        (λ Σ → Σ CTI2.⊢↓[ TE.mapPivot Fin.suc X? ] rename↓ Fin.suc c)
        (sym follows)
        (TE.conceal-renameˣ StoreRename-suc-bind c⊢)))
