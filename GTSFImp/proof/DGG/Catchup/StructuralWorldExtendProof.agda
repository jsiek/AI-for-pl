module proof.DGG.Catchup.StructuralWorldExtendProof where

-- File Charter:
--   * Erases structural right-world traces to the public extension record.
--   * Supplies the canonical one-bind bridge used by the erasure.

open import Data.Nat using (suc)
import Data.List as List
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
  renaming (subst to subst≡)

open import Types using (Ty; TyCtx)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import Reduction using
  (StoreChanges; []; _∷_; keep; bind; applyStores; applyTys)
open import proof.Reduction using (_++χ_)
open import proof.TypeInTermSubst using (renameᵗ-wk-eq)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.FuelSupportProof using
  (composeWorldExtendᴿ; mapCtxᴿ-compose)
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


composeStructuralWorldExtendᴿ : ∀ {Δᴸ Δ₀ Δ₁ Δ₂ Δ Δ₁ᵂ Δ₂ᵂ}
    {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
    {W₀ : CTI2.World Δᴸ Δ₀ Δ}
    {W₁ : CTI2.World Δᴸ Δ₁ Δ₁ᵂ}
    {W₂ : CTI2.World Δᴸ Δ₂ Δ₂ᵂ}
  → StructuralWorldExtendᴿ χs W₀ W₁
  → StructuralWorldExtendᴿ ψs W₁ W₂
  → StructuralWorldExtendᴿ (χs ++χ ψs) W₀ W₂
composeStructuralWorldExtendᴿ structural-[] plan₂ = plan₂
composeStructuralWorldExtendᴿ (structural-keep plan₁) plan₂ =
  structural-keep (composeStructuralWorldExtendᴿ plan₁ plan₂)
composeStructuralWorldExtendᴿ (structural-bind ins follows plan₁) plan₂ =
  structural-bind ins follows (composeStructuralWorldExtendᴿ plan₁ plan₂)


frozen-trace-compose : ∀ {k Δᴸ Δ₀ Δ₁ Δ₂ Δ Δ₁ᵂ Δ₂ᵂ}
    {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
    {W₀ : CTI2.World Δᴸ Δ₀ Δ}
    {W₁ : CTI2.World Δᴸ Δ₁ Δ₁ᵂ}
    {W₂ : CTI2.World Δᴸ Δ₂ Δ₂ᵂ}
    {plan₁ : StructuralWorldExtendᴿ χs W₀ W₁}
    {plan₂ : StructuralWorldExtendᴿ ψs W₁ W₂}
  → FrozenStructuralTraceᴿ k plan₁
  → FrozenStructuralTraceᴿ k plan₂
  → FrozenStructuralTraceᴿ k
      (composeStructuralWorldExtendᴿ plan₁ plan₂)
frozen-trace-compose frozen-trace-[] frozen₂ = frozen₂
frozen-trace-compose (frozen-trace-keep frozen₁) frozen₂ =
  frozen-trace-keep (frozen-trace-compose frozen₁ frozen₂)
frozen-trace-compose (frozen-trace-bind frozen-ins frozen₁) frozen₂ =
  frozen-trace-bind frozen-ins (frozen-trace-compose frozen₁ frozen₂)


record StructuralWorldExtendSplit {Δᴸ Δ₀ Δ₁ Δ₂ Δ Δ₂ᵂ}
    {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
    {W₀ : CTI2.World Δᴸ Δ₀ Δ}
    {W₂ : CTI2.World Δᴸ Δ₂ Δ₂ᵂ}
    (plan : StructuralWorldExtendᴿ (χs ++χ ψs) W₀ W₂) : Set₁ where
  field
    Δ₁ᵂ : TyCtx
    W₁ : CTI2.World Δᴸ Δ₁ Δ₁ᵂ
    prefix-plan : StructuralWorldExtendᴿ χs W₀ W₁
    suffix-plan : StructuralWorldExtendᴿ ψs W₁ W₂


splitStructuralWorldExtendᴿ : ∀ {Δᴸ Δ₀ Δ₁ Δ₂ Δ Δ₂ᵂ}
    (χs : StoreChanges Δ₀ Δ₁) {ψs : StoreChanges Δ₁ Δ₂}
    {W₀ : CTI2.World Δᴸ Δ₀ Δ}
    {W₂ : CTI2.World Δᴸ Δ₂ Δ₂ᵂ}
  → (plan : StructuralWorldExtendᴿ (χs ++χ ψs) W₀ W₂)
  → StructuralWorldExtendSplit {χs = χs} {ψs = ψs} plan
splitStructuralWorldExtendᴿ [] plan = record
  { Δ₁ᵂ = _
  ; W₁ = _
  ; prefix-plan = structural-[]
  ; suffix-plan = plan
  }
splitStructuralWorldExtendᴿ (keep ∷ χs) (structural-keep plan)
    with splitStructuralWorldExtendᴿ χs plan
splitStructuralWorldExtendᴿ (keep ∷ χs) (structural-keep plan)
    | record { Δ₁ᵂ = Δ₁ᵂ ; W₁ = W₁
             ; prefix-plan = prefix ; suffix-plan = suffix } = record
  { Δ₁ᵂ = Δ₁ᵂ
  ; W₁ = W₁
  ; prefix-plan = structural-keep prefix
  ; suffix-plan = suffix
  }
splitStructuralWorldExtendᴿ (bind B ∷ χs)
    (structural-bind ins follows plan)
    with splitStructuralWorldExtendᴿ χs plan
splitStructuralWorldExtendᴿ (bind B ∷ χs)
    (structural-bind ins follows plan)
    | record { Δ₁ᵂ = Δ₁ᵂ ; W₁ = W₁
             ; prefix-plan = prefix ; suffix-plan = suffix } = record
  { Δ₁ᵂ = Δ₁ᵂ
  ; W₁ = W₁
  ; prefix-plan = structural-bind ins follows prefix
  ; suffix-plan = suffix
  }


mapCtxᴿ-structural-compose : ∀ {Δᴸ Δ₀ Δ₁ Δ₂ Δ Δ₁ᵂ Δ₂ᵂ}
    {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
    {W₀ : CTI2.World Δᴸ Δ₀ Δ}
    {W₁ : CTI2.World Δᴸ Δ₁ Δ₁ᵂ}
    {W₂ : CTI2.World Δᴸ Δ₂ Δ₂ᵂ}
  → (plan₁ : StructuralWorldExtendᴿ χs W₀ W₁)
  → (plan₂ : StructuralWorldExtendᴿ ψs W₁ W₂)
  → (γ : CTI2.CtxImp W₀)
  → ECR.mapCtxᴿ (structural-world-extendᴿ plan₂)
      (ECR.mapCtxᴿ (structural-world-extendᴿ plan₁) γ)
      ≡ ECR.mapCtxᴿ
          (structural-world-extendᴿ
            (composeStructuralWorldExtendᴿ plan₁ plan₂))
          γ
mapCtxᴿ-structural-compose structural-[] plan₂ γ =
  cong (ECR.mapCtxᴿ (structural-world-extendᴿ plan₂))
    (ECR.mapCtxᴿ-same γ)
mapCtxᴿ-structural-compose (structural-keep plan₁) plan₂ γ =
  trans
    (cong (ECR.mapCtxᴿ (structural-world-extendᴿ plan₂))
      (mapCtxᴿ-structural-keep plan₁ γ))
    (trans
      (mapCtxᴿ-structural-compose plan₁ plan₂ γ)
      (sym (mapCtxᴿ-structural-keep
        (composeStructuralWorldExtendᴿ plan₁ plan₂) γ)))
mapCtxᴿ-structural-compose
    (structural-bind ins follows plan₁) plan₂ γ =
  trans
    (cong (ECR.mapCtxᴿ (structural-world-extendᴿ plan₂))
      (sym (mapCtxᴿ-compose insert ext₁ γ)))
    (trans
      (mapCtxᴿ-structural-compose plan₁ plan₂
        (ECR.mapCtxᴿ insert γ))
      (mapCtxᴿ-compose insert ext₂ γ))
  where
  insert = target-insert-bind-world-extendᴿ ins follows
  ext₁ = structural-world-extendᴿ plan₁
  ext₂ = structural-world-extendᴿ
    (composeStructuralWorldExtendᴿ plan₁ plan₂)
