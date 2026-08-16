module proof.DGG.Catchup.StructuralWorldExtendProof where

-- File Charter:
--   * Erases structural right-world traces to the public extension record.
--   * Supplies the canonical one-bind bridge used by the erasure.

open import Data.Nat using (suc)
import Data.List as List
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  renaming (subst to subst≡)

open import Types using (Ty)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import Reduction using
  (StoreChanges; []; _∷_; keep; bind; applyStores; applyTys)
open import proof.TypeInTermSubst using (renameᵗ-wk-eq)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.FuelSupportProof using
  (composeWorldExtendᴿ)
open import proof.DGG.Catchup.StructuralWorldExtendDef


target-insert-bind-world-extendᴿ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ (suc Δᴿ) Δ′}
    {π : Δ ↪ᵗ Δ′} {B : Ty Δᴿ}
  → (ins : TE.TargetInsert wk↪ᵗ π W W′)
  → CTI2.targetStoreʷ W′ ≡
      applyStores (bind B ∷ []) (CTI2.targetStoreʷ W)
  → ECR.WorldExtendᴿ (bind B ∷ []) W W′
target-insert-bind-world-extendᴿ {W′ = W′} ins follows = record
  { sourceStore-kept = TE.sourceStore-kept ins
  ; targetStore-follows = follows
  ; transport⊑ᵂ = λ {A = A} {C = C} p →
      subst≡ (λ C′ → A CTI2.⊑ᵂ⟨ W′ ⟩ C′)
        (renameᵗ-wk-eq C) (TE.transport⊑ᵂ ins p)
  }


prepend-keep-world-extendᴿ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
  → ECR.WorldExtendᴿ χs W W′
  → ECR.WorldExtendᴿ (keep ∷ χs) W W′
prepend-keep-world-extendᴿ ext = record
  { sourceStore-kept = ECR.sourceStore-kept ext
  ; targetStore-follows = ECR.targetStore-follows ext
  ; transport⊑ᵂ = ECR.transport⊑ᵂ ext
  }


structural-world-extendᴿ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
  → StructuralWorldExtendᴿ χs W W′
  → ECR.WorldExtendᴿ χs W W′
structural-world-extendᴿ structural-[] = ECR.sameWorldExtendᴿ
structural-world-extendᴿ (structural-keep plan) =
  prepend-keep-world-extendᴿ (structural-world-extendᴿ plan)
structural-world-extendᴿ (structural-bind ins follows plan) =
  composeWorldExtendᴿ
    (target-insert-bind-world-extendᴿ ins follows)
    (structural-world-extendᴿ plan)


mapCtxᴿ-structural-keep : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (γ : CTI2.CtxImp W)
  → ECR.mapCtxᴿ (structural-world-extendᴿ (structural-keep plan)) γ
      ≡ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
mapCtxᴿ-structural-keep plan γ =
  mapCtxᴿ-prepend-keep (structural-world-extendᴿ plan) γ
  where
  mapCtxᴿ-prepend-keep : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {W : CTI2.World Δᴸ Δᴿ Δ}
      {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    → (ext : ECR.WorldExtendᴿ χs W W′)
    → (γ : CTI2.CtxImp W)
    → ECR.mapCtxᴿ (prepend-keep-world-extendᴿ ext) γ
        ≡ ECR.mapCtxᴿ ext γ
  mapCtxᴿ-prepend-keep ext List.[] = refl
  mapCtxᴿ-prepend-keep {χs = χs} ext
      (CTI2.ctx-imp A B p List.∷ γ) =
    cong (λ γ′ →
      CTI2.ctx-imp A (applyTys χs B) (ECR.transport⊑ᵂ ext p)
        List.∷ γ′)
      (mapCtxᴿ-prepend-keep ext γ)
