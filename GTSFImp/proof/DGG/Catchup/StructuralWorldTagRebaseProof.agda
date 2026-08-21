module proof.DGG.Catchup.StructuralWorldTagRebaseProof where

-- File Charter:
--   * Transforms a structural target-extension trace through source conceal.
--   * Preserves the reverse tag-rebase orientation and maps its target pivot.

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Reduction using ([]; _∷_; bind; applyStores)
import proof.DGG.CtxImp as CTI2
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
  → StructuralTagRebaseAtᴸReplay plan rb
  → StructuralTagRebaseAtᴸResult plan rb
structural-tag-rebase-atᴸ structural-[] rb tag-rebase-[] = record
  { Wᵖ′ = _
  ; premise-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-tag-rebase-atᴸ (structural-keep plan) rb
    (tag-rebase-keep replay)
    with structural-tag-rebase-atᴸ plan rb replay
structural-tag-rebase-atᴸ (structural-keep plan) rb
    (tag-rebase-keep replay)
    | record { Wᵖ′ = Wᵖ′ ; premise-plan = planᵖ
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Wᵖ′ = Wᵖ′
    ; premise-plan = structural-keep planᵖ
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-tag-rebase-atᴸ
    (structural-bind {B = B} ins follows plan) rb
    (tag-rebase-bind insᵖ rb₁ replay)
    with structural-tag-rebase-atᴸ plan rb₁ replay
structural-tag-rebase-atᴸ
    (structural-bind {B = B} ins follows plan) rb
    (tag-rebase-bind insᵖ rb₁ replay)
    | record { Wᵖ′ = Wᵖ′ ; premise-plan = planᵖ
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Wᵖ′ = Wᵖ′
    ; premise-plan = structural-bind insᵖ followsᵖ planᵖ
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert ins insᵖ mono)
    }
  where
  followsᵖ =
    trans (sym (CTI2T.rebaseᴸ-target-store
      (CTI2.forgetTagRebaseᴸ rb₁)))
      (trans follows
        (cong (applyStores (bind B ∷ []))
          (CTI2T.rebaseᴸ-target-store
            (CTI2.forgetTagRebaseᴸ rb))))


structural-tag-rebase-atᴸ-pullback : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : Reduction.StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → StructuralTagRebaseAtᴸPullbackReplay planᵖ rb
  → StructuralTagRebaseAtᴸPullbackResult planᵖ rb
structural-tag-rebase-atᴸ-pullback structural-[] rb tag-pullback-[] = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-tag-rebase-atᴸ-pullback (structural-keep planᵖ) rb
    (tag-pullback-keep replay)
    with structural-tag-rebase-atᴸ-pullback planᵖ rb replay
structural-tag-rebase-atᴸ-pullback (structural-keep planᵖ) rb
    (tag-pullback-keep replay)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-keep plan
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    rb (tag-pullback-bind ins rb₁ replay)
    with structural-tag-rebase-atᴸ-pullback planᵖ rb₁ replay
structural-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    rb (tag-pullback-bind ins rb₁ replay)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind ins follows plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert ins insᵖ mono)
    }
  where
  follows =
    trans (CTI2T.rebaseᴸ-target-store
      (CTI2.forgetTagRebaseᴸ rb₁))
      (trans followsᵖ
        (cong (applyStores (bind B ∷ []))
          (sym (CTI2T.rebaseᴸ-target-store
            (CTI2.forgetTagRebaseᴸ rb)))))
