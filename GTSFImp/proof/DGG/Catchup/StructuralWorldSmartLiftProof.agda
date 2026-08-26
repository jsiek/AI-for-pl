module proof.DGG.Catchup.StructuralWorldSmartLiftProof where

-- File Charter:
--   * Transforms a structural target-extension trace through source Λ.
--   * Handles smart-alias and smart-fresh guards without a numeric rank.

open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Nat using (suc)

open import Reduction using ([]; _∷_; bind; applyStores)
import proof.DGG.CtxImp as CTI2
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldSmartLiftDef


structural-smart-liftᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {χs : Reduction.StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (liftW : CTI2.SmartCommaLiftᴸ W Wᵐ)
  → StructuralSmartLiftᴸResult plan liftW
structural-smart-liftᴸ structural-[] liftW = record
  { Δᵐ′ = _
  ; Wᵐ′ = _
  ; premise-plan = structural-[]
  ; post-lift = liftW
  }
structural-smart-liftᴸ (structural-keep plan) liftW
    with structural-smart-liftᴸ plan liftW
structural-smart-liftᴸ (structural-keep plan) liftW
    | record { Δᵐ′ = Δᵐ′ ; Wᵐ′ = Wᵐ′ ; premise-plan = planᵐ
             ; post-lift = liftW′ } =
  record
    { Δᵐ′ = Δᵐ′
    ; Wᵐ′ = Wᵐ′
    ; premise-plan = structural-keep planᵐ
    ; post-lift = liftW′
    }
structural-smart-liftᴸ
    (structural-bind {B = B} ins follows plan)
    (CTI2.smart-merge-alias guard)
    with structural-smart-liftᴸ plan
      (CTI2.smart-merge-alias (TE.smartAliasGuardInsert ins guard))
structural-smart-liftᴸ
    (structural-bind {B = B} ins follows plan)
    (CTI2.smart-merge-alias guard)
    | record { Δᵐ′ = Δᵐ′ ; Wᵐ′ = Wᵐ′ ; premise-plan = planᵐ
             ; post-lift = liftW′ } =
  record
    { Δᵐ′ = Δᵐ′
    ; Wᵐ′ = Wᵐ′
    ; premise-plan = structural-bind
        (TE.smartAliasTargetInsert ins guard) followsᵐ planᵐ
    ; post-lift = liftW′
    }
  where
  followsᵐ =
    trans (CTI2.SmartAliasMergeGuard.targetStore-same
      (TE.smartAliasGuardInsert ins guard))
      (trans follows
        (cong (applyStores (bind B ∷ []))
          (sym (CTI2.SmartAliasMergeGuard.targetStore-same guard))))
structural-smart-liftᴸ
    (structural-bind {B = B} ins follows plan)
    (CTI2.smart-fresh-behind guard)
    with structural-smart-liftᴸ plan
      (CTI2.smart-fresh-behind (TE.smartFreshGuardInsert ins guard))
structural-smart-liftᴸ
    (structural-bind {B = B} ins follows plan)
    (CTI2.smart-fresh-behind guard)
    | record { Δᵐ′ = Δᵐ′ ; Wᵐ′ = Wᵐ′ ; premise-plan = planᵐ
             ; post-lift = liftW′ } =
  record
    { Δᵐ′ = Δᵐ′
    ; Wᵐ′ = Wᵐ′
    ; premise-plan = structural-bind
        (TE.smartFreshTargetInsert ins guard) followsᵐ planᵐ
    ; post-lift = liftW′
    }
  where
  followsᵐ =
    trans (CTI2.SmartFreshBehindGuard.targetStore-same
      (TE.smartFreshGuardInsert ins guard))
      (trans follows
        (cong (applyStores (bind B ∷ []))
          (sym (CTI2.SmartFreshBehindGuard.targetStore-same guard))))
