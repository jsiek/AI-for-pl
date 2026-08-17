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
  ; post-mono = λ mono → mono
  }
structural-tag-rebase-atᴸ (structural-keep plan) rb
    with structural-tag-rebase-atᴸ plan rb
structural-tag-rebase-atᴸ (structural-keep plan) rb
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
    with TE.reverseTagRebaseAtᴸ ins rb
structural-tag-rebase-atᴸ
    (structural-bind {B = B} ins follows plan) rb
    | Wᵖ₁ , insᵖ , rb₁
    with structural-tag-rebase-atᴸ plan rb₁
structural-tag-rebase-atᴸ
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
  → StructuralTagRebaseAtᴸPullbackResult planᵖ rb
structural-tag-rebase-atᴸ-pullback structural-[] rb = record
  { W′ = _
  ; outer-plan = structural-[]
  ; post-rebase = rb
  ; post-mono = λ mono → mono
  }
structural-tag-rebase-atᴸ-pullback (structural-keep planᵖ) rb
    with structural-tag-rebase-atᴸ-pullback planᵖ rb
structural-tag-rebase-atᴸ-pullback (structural-keep planᵖ) rb
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
    CTI2.tag-rebase-idᴸ
    with structural-tag-rebase-atᴸ-pullback
      planᵖ CTI2.tag-rebase-idᴸ
structural-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    CTI2.tag-rebase-idᴸ
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind insᵖ followsᵖ plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert insᵖ insᵖ mono)
    }
structural-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.tag-rebase-varᴸ rb)
    with structural-tag-rebase-atᴸ-pullback planᵖ
      (CTI2.tag-rebase-varᴸ (TE.pullbackReverseRebaseAt insᵖ rb))
structural-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.tag-rebase-varᴸ rb)
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

  -- The fresh target bind is to the right of every old pivot.  In the
  -- source-conceal orientation, target freezing is used in reverse to leave
  -- the premise pivot under `wk` and reconstruct the outer insert.
  follows =
    trans followsᵖ
      (cong (applyStores (bind B ∷ []))
        (sym (CTI2T.rebase-target-store rb)))
structural-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented)
    with structural-tag-rebase-atᴸ-pullback planᵖ
      (CTI2.tag-rebase-onlyᴸ
        (TE.insert-to-starᴸ insᵖ to-star)
        (TE.insert-disalignedᴸ insᵖ disaligned)
        (TE.insert-represented★ᴸ insᵖ represented))
structural-tag-rebase-atᴸ-pullback
    (structural-bind {B = B} insᵖ followsᵖ planᵖ)
    (CTI2.tag-rebase-onlyᴸ to-star disaligned represented)
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { W′ = W′
    ; outer-plan = structural-bind insᵖ followsᵖ plan
    ; post-rebase = rb′
    ; post-mono = λ mono → mono′ (TE.impEnvMono-insert insᵖ insᵖ mono)
    }
