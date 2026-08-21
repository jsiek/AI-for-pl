module proof.DGG.Catchup.StructuralWorldTagRebaseDef where

-- File Charter:
--   * States structural extension transport through a source tag rebase.
--   * Tracks the target pivot through every target-side store change.

open import Data.Maybe using (Maybe)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyVar)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import Reduction using
  (StoreChanges; []; _∷_; bind; applyStores)
import proof.DGG.CtxImp as CTI2
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralWorldExtendDef public using
  ( StructuralWorldExtendᴿ
  ; structural-[]
  ; structural-keep
  ; structural-bind
  ; mapPivotChanges
  ; mapPivotChanges-++
  ; mapVarChanges
  )


record StructuralTagRebaseAtᴸResult
    {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    (plan : StructuralWorldExtendᴿ χs W W′)
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
    (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?) : Set₁ where
  field
    Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′
    premise-plan : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′
    post-rebase : CTI2.TagRebaseAtᴸ Wᵖ′ W′ Xᴸ?
      (mapPivotChanges χs Xᴿ?)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


record StructuralTagRebaseAtᴸPullbackResult
    {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
    {W : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
    (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?) : Set₁ where
  field
    W′ : CTI2.World Δᴸ Δᴿ′ Δ′
    outer-plan : StructuralWorldExtendᴿ χs W W′
    post-rebase : CTI2.TagRebaseAtᴸ Wᵖ′ W′ Xᴸ?
      (mapPivotChanges χs Xᴿ?)
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′


data StructuralTagRebaseAtᴸReplay { Δᴸ } :
    ∀ {Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {W : CTI2.World Δᴸ Δᴿ Δ}
      {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
      {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    → (plan : StructuralWorldExtendᴿ χs W W′)
    → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
    → Set₁ where

  tag-rebase-[] : ∀ {Δᴿ Δ}
      {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
      {rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?}
    → StructuralTagRebaseAtᴸReplay (structural-[] {W = W}) rb

  tag-rebase-keep : ∀ {Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {W : CTI2.World Δᴸ Δᴿ Δ}
      {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
      {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
      {plan : StructuralWorldExtendᴿ χs W W′}
      {rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?}
    → StructuralTagRebaseAtᴸReplay plan rb
    → StructuralTagRebaseAtᴸReplay (structural-keep plan) rb

  tag-rebase-bind : ∀ {Δᴿ Δᴿ′ Δ Δ₁ Δ′}
      {B : Ty Δᴿ} {π : Δ ↪ᵗ Δ₁}
      {χs : StoreChanges (suc Δᴿ) Δᴿ′}
      {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
      {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
      {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
      {ins : TE.TargetInsert wk↪ᵗ π W W₁}
      {follows : CTI2.targetStoreʷ W₁ ≡
        applyStores (bind B ∷ []) (CTI2.targetStoreʷ W)}
      {plan : StructuralWorldExtendᴿ χs W₁ W′}
      {rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?}
      {Wᵖ₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    → (insᵖ : TE.TargetInsert wk↪ᵗ π Wᵖ Wᵖ₁)
    → (rb₁ : CTI2.TagRebaseAtᴸ Wᵖ₁ W₁ Xᴸ?
        (mapPivotChanges (bind B ∷ []) Xᴿ?))
    → StructuralTagRebaseAtᴸReplay plan rb₁
    → StructuralTagRebaseAtᴸReplay
        (structural-bind ins follows plan) rb


data StructuralTagRebaseAtᴸPullbackReplay { Δᴸ } :
    ∀ {Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
      {W : CTI2.World Δᴸ Δᴿ Δ}
      {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    → (planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′)
    → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
    → Set₁ where

  tag-pullback-[] : ∀ {Δᴿ Δ}
      {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
      {rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?}
    → StructuralTagRebaseAtᴸPullbackReplay
        (structural-[] {W = Wᵖ}) rb

  tag-pullback-keep : ∀ {Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
      {W : CTI2.World Δᴸ Δᴿ Δ}
      {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
      {planᵖ : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′}
      {rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?}
    → StructuralTagRebaseAtᴸPullbackReplay planᵖ rb
    → StructuralTagRebaseAtᴸPullbackReplay
        (structural-keep planᵖ) rb

  tag-pullback-bind : ∀ {Δᴿ Δᴿ′ Δ Δ₁ Δ′}
      {B : Ty Δᴿ} {π : Δ ↪ᵗ Δ₁}
      {χs : StoreChanges (suc Δᴿ) Δᴿ′}
      {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {Wᵖ₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
      {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δ′}
      {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
      {insᵖ : TE.TargetInsert wk↪ᵗ π Wᵖ Wᵖ₁}
      {followsᵖ : CTI2.targetStoreʷ Wᵖ₁ ≡
        applyStores (bind B ∷ []) (CTI2.targetStoreʷ Wᵖ)}
      {planᵖ : StructuralWorldExtendᴿ χs Wᵖ₁ Wᵖ′}
      {rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?}
      {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
    → (rb₁ : CTI2.TagRebaseAtᴸ Wᵖ₁ W₁ Xᴸ?
        (mapPivotChanges (bind B ∷ []) Xᴿ?))
    → StructuralTagRebaseAtᴸPullbackReplay planᵖ rb₁
    → StructuralTagRebaseAtᴸPullbackReplay
        (structural-bind insᵖ followsᵖ planᵖ) rb
