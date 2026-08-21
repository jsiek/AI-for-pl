module proof.DGG.Catchup.StructuralWorldRebaseProof where

-- File Charter:
--   * Transforms a structural target-extension trace through source rebase.
--   * Returns the premise trace and the rebase at its final world.

open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Product using (_,_)

open import Reduction using
  (StoreChanges; []; _∷_; bind; applyStores)
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralWorldExtendDef


structural-rebase-atᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ?}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?)
  → StructuralRebaseAtᴸReplay plan rb
  → StructuralRebaseAtᴸResult plan rb
structural-rebase-atᴸ structural-[] rb rebaseᴸ-replay-[] = record
  { Wᵖ′ = _
  ; premise-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-rebase-atᴸ (structural-keep plan) rb
    (rebaseᴸ-replay-keep replay)
    with structural-rebase-atᴸ plan rb replay
structural-rebase-atᴸ (structural-keep plan) rb
    (rebaseᴸ-replay-keep replay)
    | record { Wᵖ′ = Wᵖ′ ; premise-plan = planᵖ
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Wᵖ′ = Wᵖ′
    ; premise-plan = structural-keep planᵖ
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-rebase-atᴸ (structural-bind {B = B} ins follows plan) rb
    (rebaseᴸ-replay-bind insᵖ rb₁ replay)
    with structural-rebase-atᴸ plan rb₁ replay
structural-rebase-atᴸ (structural-bind {B = B} ins follows plan) rb
    (rebaseᴸ-replay-bind insᵖ rb₁ replay)
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
    trans (CTI2T.rebaseᴸ-target-store rb₁)
      (trans follows
        (cong (applyStores (bind B ∷ []))
          (sym (CTI2T.rebaseᴸ-target-store rb))))


structural-rebase-atᴸ-pullback : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ?}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?)
  → StructuralRebaseAtᴸPullbackReplay planᵖ rb
  → StructuralRebaseAtᴸPullbackResult planᵖ rb
structural-rebase-atᴸ-pullback structural-[] rb rebaseᴸ-pullback-[] = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-rebase-atᴸ-pullback (structural-keep planᵖ) rb
    (rebaseᴸ-pullback-keep replay)
    with structural-rebase-atᴸ-pullback planᵖ rb replay
structural-rebase-atᴸ-pullback (structural-keep planᵖ) rb
    (rebaseᴸ-pullback-keep replay)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-keep plan
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) rb
    (rebaseᴸ-pullback-bind ins rb₁ replay)
    with structural-rebase-atᴸ-pullback planᵖ rb₁ replay
structural-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) rb
    (rebaseᴸ-pullback-bind ins rb₁ replay)
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
    trans (sym (CTI2T.rebaseᴸ-target-store rb₁))
      (trans followsᵖ
        (cong (applyStores (bind B ∷ []))
          (CTI2T.rebaseᴸ-target-store rb)))


structural-rebase-atᴿ-pullback : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴿ?}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : CTI2.RebaseAtᴿ W Wᵖ Xᴿ?)
  → StructuralRebaseAtᴿPullbackReplay planᵖ rb
  → StructuralRebaseAtᴿPullbackResult planᵖ rb
structural-rebase-atᴿ-pullback structural-[] rb rebaseᴿ-pullback-[] = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-rebase-atᴿ-pullback (structural-keep planᵖ) rb
    (rebaseᴿ-pullback-keep replay)
    with structural-rebase-atᴿ-pullback planᵖ rb replay
structural-rebase-atᴿ-pullback (structural-keep planᵖ) rb
    (rebaseᴿ-pullback-keep replay)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-keep plan
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-rebase-atᴿ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) rb
    (rebaseᴿ-pullback-bind ins rb₁ replay)
    with structural-rebase-atᴿ-pullback planᵖ rb₁ replay
structural-rebase-atᴿ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) rb
    (rebaseᴿ-pullback-bind ins rb₁ replay)
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
    trans (sym (CTI2T.rebaseᴿ-target-store rb₁))
      (trans followsᵖ
        (cong (applyStores (bind B ∷ []))
          (CTI2T.rebaseᴿ-target-store rb)))


structural-rebase-at-pullback : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → StructuralRebaseAtPullbackReplay planᵖ rb
  → StructuralRebaseAtPullbackResult planᵖ rb
structural-rebase-at-pullback structural-[] rb rebase-pullback-[] = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-rebase-at-pullback (structural-keep planᵖ) rb
    (rebase-pullback-keep replay)
    with structural-rebase-at-pullback planᵖ rb replay
structural-rebase-at-pullback (structural-keep planᵖ) rb
    (rebase-pullback-keep replay)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-keep plan
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-rebase-at-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) rb
    (rebase-pullback-bind ins rb₁ replay)
    with structural-rebase-at-pullback planᵖ rb₁ replay
structural-rebase-at-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) rb
    (rebase-pullback-bind ins rb₁ replay)
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
    trans (sym (CTI2T.rebase-target-store rb₁))
      (trans followsᵖ
        (cong (applyStores (bind B ∷ []))
          (CTI2T.rebase-target-store rb)))


structural-reverse-rebase-atᴿ-pullback : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴿ?}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : CTI2.RebaseAtᴿ Wᵖ W Xᴿ?)
  → StructuralReverseRebaseAtᴿPullbackReplay planᵖ rb
  → StructuralReverseRebaseAtᴿPullbackResult planᵖ rb
structural-reverse-rebase-atᴿ-pullback structural-[] rb
    reverse-rebaseᴿ-pullback-[] = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-reverse-rebase-atᴿ-pullback (structural-keep planᵖ) rb
    (reverse-rebaseᴿ-pullback-keep replay)
    with structural-reverse-rebase-atᴿ-pullback planᵖ rb replay
structural-reverse-rebase-atᴿ-pullback (structural-keep planᵖ) rb
    (reverse-rebaseᴿ-pullback-keep replay)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-keep plan
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-reverse-rebase-atᴿ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) rb
    (reverse-rebaseᴿ-pullback-bind ins rb₁ replay)
    with structural-reverse-rebase-atᴿ-pullback planᵖ rb₁ replay
structural-reverse-rebase-atᴿ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) rb
    (reverse-rebaseᴿ-pullback-bind ins rb₁ replay)
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
    trans (CTI2T.rebaseᴿ-target-store rb₁)
      (trans followsᵖ
        (cong (applyStores (bind B ∷ []))
          (sym (CTI2T.rebaseᴿ-target-store rb))))


structural-reverse-rebase-at-pullback : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → StructuralReverseRebaseAtPullbackReplay planᵖ rb
  → StructuralReverseRebaseAtPullbackResult planᵖ rb
structural-reverse-rebase-at-pullback structural-[] rb
    reverse-rebase-pullback-[] = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-reverse-rebase-at-pullback (structural-keep planᵖ) rb
    (reverse-rebase-pullback-keep replay)
    with structural-reverse-rebase-at-pullback planᵖ rb replay
structural-reverse-rebase-at-pullback (structural-keep planᵖ) rb
    (reverse-rebase-pullback-keep replay)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-keep plan
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-reverse-rebase-at-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) rb
    (reverse-rebase-pullback-bind ins rb₁ replay)
    with structural-reverse-rebase-at-pullback planᵖ rb₁ replay
structural-reverse-rebase-at-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) rb
    (reverse-rebase-pullback-bind ins rb₁ replay)
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
    trans (CTI2T.rebase-target-store rb₁)
      (trans followsᵖ
        (cong (applyStores (bind B ∷ []))
          (sym (CTI2T.rebase-target-store rb))))
