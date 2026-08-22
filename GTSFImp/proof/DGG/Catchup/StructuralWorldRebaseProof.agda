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
  → StructuralRebaseAtᴸResult plan rb
structural-rebase-atᴸ structural-[] rb = record
  { Wᵖ′ = _
  ; premise-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-rebase-atᴸ (structural-keep plan) rb
    with structural-rebase-atᴸ plan rb
structural-rebase-atᴸ (structural-keep plan) rb
    | record { Wᵖ′ = Wᵖ′ ; premise-plan = planᵖ
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Wᵖ′ = Wᵖ′
    ; premise-plan = structural-keep planᵖ
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-rebase-atᴸ (structural-bind {B = B} ins follows plan) rb
    with TE.insertRebaseAtᴸ ins rb
structural-rebase-atᴸ (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
    with structural-rebase-atᴸ plan rb₁
structural-rebase-atᴸ (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
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


structural-rebase-atᴿ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴿ?}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (rb : CTI2.RebaseAtᴿ W Wᵖ Xᴿ?)
  → StructuralRebaseAtᴿResult plan rb
structural-rebase-atᴿ structural-[] rb = record
  { Wᵖ′ = _
  ; premise-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-rebase-atᴿ (structural-keep plan) rb
    with structural-rebase-atᴿ plan rb
structural-rebase-atᴿ (structural-keep plan) rb
    | record { Wᵖ′ = Wᵖ′ ; premise-plan = planᵖ
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Wᵖ′ = Wᵖ′
    ; premise-plan = structural-keep planᵖ
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-rebase-atᴿ (structural-bind {B = B} ins follows plan) rb
    with TE.insertRebaseAtᴿ ins rb
structural-rebase-atᴿ (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
    with structural-rebase-atᴿ plan rb₁
structural-rebase-atᴿ (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
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
    trans (CTI2T.rebaseᴿ-target-store rb₁)
      (trans follows
        (cong (applyStores (bind B ∷ []))
          (sym (CTI2T.rebaseᴿ-target-store rb))))


structural-rebase-at : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → StructuralRebaseAtResult plan rb
structural-rebase-at structural-[] rb = record
  { Wᵖ′ = _
  ; premise-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-rebase-at (structural-keep plan) rb
    with structural-rebase-at plan rb
structural-rebase-at (structural-keep plan) rb
    | record { Wᵖ′ = Wᵖ′ ; premise-plan = planᵖ
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Wᵖ′ = Wᵖ′
    ; premise-plan = structural-keep planᵖ
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-rebase-at (structural-bind {B = B} ins follows plan) rb
    with TE.insertRebaseAt ins rb
structural-rebase-at (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
    with structural-rebase-at plan rb₁
structural-rebase-at (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
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
    trans (CTI2T.rebase-target-store rb₁)
      (trans follows
        (cong (applyStores (bind B ∷ []))
          (sym (CTI2T.rebase-target-store rb))))


structural-reverse-rebase-atᴿ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴿ?}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (rb : CTI2.RebaseAtᴿ Wᵖ W Xᴿ?)
  → StructuralReverseRebaseAtᴿResult plan rb
structural-reverse-rebase-atᴿ structural-[] rb = record
  { Wᵖ′ = _
  ; premise-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-reverse-rebase-atᴿ (structural-keep plan) rb
    with structural-reverse-rebase-atᴿ plan rb
structural-reverse-rebase-atᴿ (structural-keep plan) rb
    | record { Wᵖ′ = Wᵖ′ ; premise-plan = planᵖ
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Wᵖ′ = Wᵖ′
    ; premise-plan = structural-keep planᵖ
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-reverse-rebase-atᴿ
    (structural-bind {B = B} ins follows plan) rb
    with TE.reverseRebaseAtᴿ ins rb
structural-reverse-rebase-atᴿ
    (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
    with structural-reverse-rebase-atᴿ plan rb₁
structural-reverse-rebase-atᴿ
    (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
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
    trans (sym (CTI2T.rebaseᴿ-target-store rb₁))
      (trans follows
        (cong (applyStores (bind B ∷ []))
          (CTI2T.rebaseᴿ-target-store rb)))


structural-reverse-rebase-at : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (rb : CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → StructuralReverseRebaseAtResult plan rb
structural-reverse-rebase-at structural-[] rb = record
  { Wᵖ′ = _
  ; premise-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-reverse-rebase-at (structural-keep plan) rb
    with structural-reverse-rebase-at plan rb
structural-reverse-rebase-at (structural-keep plan) rb
    | record { Wᵖ′ = Wᵖ′ ; premise-plan = planᵖ
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Wᵖ′ = Wᵖ′
    ; premise-plan = structural-keep planᵖ
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-reverse-rebase-at
    (structural-bind {B = B} ins follows plan) rb
    with TE.reverseRebaseAt ins rb
structural-reverse-rebase-at
    (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
    with structural-reverse-rebase-at plan rb₁
structural-reverse-rebase-at
    (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
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
    trans (sym (CTI2T.rebase-target-store rb₁))
      (trans follows
        (cong (applyStores (bind B ∷ []))
          (CTI2T.rebase-target-store rb)))


structural-rebase-atᴸ-pullback : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ?}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?)
  → StructuralRebaseAtᴸPullbackResult planᵖ rb
structural-rebase-atᴸ-pullback structural-[] rb = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-rebase-atᴸ-pullback (structural-keep planᵖ) rb
    with structural-rebase-atᴸ-pullback planᵖ rb
structural-rebase-atᴸ-pullback (structural-keep planᵖ) rb
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-keep plan
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) CTI2.rebase-idᴸ
    with structural-rebase-atᴸ-pullback planᵖ CTI2.rebase-idᴸ
structural-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) CTI2.rebase-idᴸ
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind insᵖ followsᵖ plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert insᵖ insᵖ mono)
    }


structural-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.rebase-varᴸ rb)
    with structural-rebase-atᴸ-pullback planᵖ
      (CTI2.rebase-varᴸ (TE.pullbackRebaseAt insᵖ rb))
structural-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.rebase-varᴸ rb)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind ins follows plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert ins insᵖ mono)
    }
  where
  ins = TE.pullbackRebaseTargetInsert insᵖ rb

  -- The bind center is fresh on the target side.  The source rebase can only
  -- pivot at an old source/target center, so the pullback uses target
  -- freezing to commute the old pivot under the fresh `wk` insertion.
  follows =
    trans followsᵖ
      (cong (applyStores (bind B ∷ []))
        (CTI2T.rebase-target-store rb))
structural-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.rebase-onlyᴸ to-star disaligned represented)
    with structural-rebase-atᴸ-pullback planᵖ
      (CTI2.rebase-onlyᴸ
        (TE.insert-to-starᴸ insᵖ to-star)
        (TE.insert-disalignedᴸ insᵖ disaligned)
        (TE.insert-represented★ᴸ insᵖ represented))
structural-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.rebase-onlyᴸ to-star disaligned represented)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind insᵖ followsᵖ plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert insᵖ insᵖ mono)
    }


structural-rebase-atᴿ-pullback : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴿ?}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : CTI2.RebaseAtᴿ W Wᵖ Xᴿ?)
  → StructuralRebaseAtᴿPullbackResult planᵖ rb
structural-rebase-atᴿ-pullback structural-[] rb = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-rebase-atᴿ-pullback (structural-keep planᵖ) rb
    with structural-rebase-atᴿ-pullback planᵖ rb
structural-rebase-atᴿ-pullback (structural-keep planᵖ) rb
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-keep plan
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-rebase-atᴿ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) CTI2.rebase-idᴿ
    with structural-rebase-atᴿ-pullback planᵖ CTI2.rebase-idᴿ
structural-rebase-atᴿ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) CTI2.rebase-idᴿ
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind insᵖ followsᵖ plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert insᵖ insᵖ mono)
    }
structural-rebase-atᴿ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.rebase-varᴿ rb)
    with structural-rebase-atᴿ-pullback planᵖ
      (CTI2.rebase-varᴿ (TE.pullbackRebaseAt insᵖ rb))
structural-rebase-atᴿ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.rebase-varᴿ rb)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind ins follows plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert ins insᵖ mono)
    }
  where
  ins = TE.pullbackRebaseTargetInsert insᵖ rb

  follows =
    trans followsᵖ
      (cong (applyStores (bind B ∷ []))
        (CTI2T.rebase-target-store rb))


structural-rebase-at-pullback : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → StructuralRebaseAtPullbackResult planᵖ rb
structural-rebase-at-pullback structural-[] rb = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-rebase-at-pullback (structural-keep planᵖ) rb
    with structural-rebase-at-pullback planᵖ rb
structural-rebase-at-pullback (structural-keep planᵖ) rb
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
    with structural-rebase-at-pullback planᵖ
      (TE.pullbackRebaseAt insᵖ rb)
structural-rebase-at-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) rb
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind ins follows plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert ins insᵖ mono)
    }
  where
  ins = TE.pullbackRebaseTargetInsert insᵖ rb

  follows =
    trans followsᵖ
      (cong (applyStores (bind B ∷ []))
        (CTI2T.rebase-target-store rb))


structural-reverse-rebase-atᴿ-pullback : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴿ?}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : CTI2.RebaseAtᴿ Wᵖ W Xᴿ?)
  → StructuralReverseRebaseAtᴿPullbackResult planᵖ rb
structural-reverse-rebase-atᴿ-pullback structural-[] rb = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-reverse-rebase-atᴿ-pullback (structural-keep planᵖ) rb
    with structural-reverse-rebase-atᴿ-pullback planᵖ rb
structural-reverse-rebase-atᴿ-pullback (structural-keep planᵖ) rb
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-keep plan
    ; post-rebase = rb′
    ; post-mono = mono′
    }
structural-reverse-rebase-atᴿ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) CTI2.rebase-idᴿ
    with structural-reverse-rebase-atᴿ-pullback planᵖ CTI2.rebase-idᴿ
structural-reverse-rebase-atᴿ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) CTI2.rebase-idᴿ
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind insᵖ followsᵖ plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert insᵖ insᵖ mono)
    }
structural-reverse-rebase-atᴿ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.rebase-varᴿ rb)
    with structural-reverse-rebase-atᴿ-pullback planᵖ
      (CTI2.rebase-varᴿ (TE.pullbackReverseRebaseAt insᵖ rb))
structural-reverse-rebase-atᴿ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.rebase-varᴿ rb)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind ins follows plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert ins insᵖ mono)
    }
  where
  ins = TE.pullbackReverseRebaseTargetInsert insᵖ rb

  follows =
    trans followsᵖ
      (cong (applyStores (bind B ∷ []))
        (sym (CTI2T.rebase-target-store rb)))


structural-reverse-rebase-at-pullback : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
  → (rb : CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → StructuralReverseRebaseAtPullbackResult planᵖ rb
structural-reverse-rebase-at-pullback structural-[] rb = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-reverse-rebase-at-pullback (structural-keep planᵖ) rb
    with structural-reverse-rebase-at-pullback planᵖ rb
structural-reverse-rebase-at-pullback (structural-keep planᵖ) rb
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
    with structural-reverse-rebase-at-pullback planᵖ
      (TE.pullbackReverseRebaseAt insᵖ rb)
structural-reverse-rebase-at-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ) rb
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind ins follows plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert ins insᵖ mono)
    }
  where
  ins = TE.pullbackReverseRebaseTargetInsert insᵖ rb

  follows =
    trans followsᵖ
      (cong (applyStores (bind B ∷ []))
        (sym (CTI2T.rebase-target-store rb)))
