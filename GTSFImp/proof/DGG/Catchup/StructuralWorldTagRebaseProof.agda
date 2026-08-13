module proof.DGG.Catchup.StructuralWorldTagRebaseProof where

-- File Charter:
--   * Transforms a structural target-extension trace through source conceal.
--   * Preserves the reverse tag-rebase orientation and maps its target pivot.

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Reduction using ([]; _∷_; bind; applyStores)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef


structural-tag-rebase-atᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : Reduction.StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → StructuralTagRebaseAtᴸResult plan rb
structural-tag-rebase-atᴸ structural-[] rb = record
  { Wᵖ′ = _
  ; premise-plan = structural-[]
  ; post-rebase = rb
  }
structural-tag-rebase-atᴸ (structural-keep plan) rb
    with structural-tag-rebase-atᴸ plan rb
structural-tag-rebase-atᴸ (structural-keep plan) rb
    | record { Wᵖ′ = Wᵖ′ ; premise-plan = planᵖ
             ; post-rebase = rb′ } =
  record
    { Wᵖ′ = Wᵖ′
    ; premise-plan = structural-keep planᵖ
    ; post-rebase = rb′
    }
structural-tag-rebase-atᴸ
    (structural-bind {B = B} ins follows plan) rb
    with TE.reverseTagRebaseAtᴸ ins rb
structural-tag-rebase-atᴸ
    (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
    with structural-tag-rebase-atᴸ plan rb₁
structural-tag-rebase-atᴸ
    (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
    | record { Wᵖ′ = Wᵖ′ ; premise-plan = planᵖ
             ; post-rebase = rb′ } =
  record
    { Wᵖ′ = Wᵖ′
    ; premise-plan = structural-bind insᵖ followsᵖ planᵖ
    ; post-rebase = rb′
    }
  where
  followsᵖ =
    trans (sym (CTI2T.rebaseᴸ-target-store
      (CTI2.forgetTagRebaseᴸ rb₁)))
      (trans follows
        (cong (applyStores (bind B ∷ []))
          (CTI2T.rebaseᴸ-target-store
            (CTI2.forgetTagRebaseᴸ rb))))
