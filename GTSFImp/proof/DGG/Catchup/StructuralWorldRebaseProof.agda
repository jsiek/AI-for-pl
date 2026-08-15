module proof.DGG.Catchup.StructuralWorldRebaseProof where

-- File Charter:
--   * Transforms a structural target-extension trace through source rebase.
--   * Returns the premise trace and the rebase at its final world.

open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Product using (_,_)

open import Reduction using
  (StoreChanges; []; _∷_; bind; applyStores)
import proof.DGG.CastTermImprecision2 as CTI2
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
