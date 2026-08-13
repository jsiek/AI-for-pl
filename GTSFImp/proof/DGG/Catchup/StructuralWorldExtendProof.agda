module proof.DGG.Catchup.StructuralWorldExtendProof where

-- File Charter:
--   * Erases structural right-world traces to the public extension record.
--   * Supplies the canonical one-bind bridge used by the erasure.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (subst to subst≡)

open import Types using (Ty)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import Reduction using (StoreChanges; []; _∷_; bind; applyStores)
open import proof.TypeInTermSubst using (renameᵗ-wk-eq)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.ValueCatchupRightDef using (_++χ_)
open import proof.DGG.Catchup.ColumnSupportProof using
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


structural-world-extendᴿ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
  → StructuralWorldExtendᴿ χs W W′
  → ECR.WorldExtendᴿ χs W W′
structural-world-extendᴿ structural-[] = ECR.sameWorldExtendᴿ
structural-world-extendᴿ (structural-keep plan) =
  composeWorldExtendᴿ ECR.sameWorldKeepExtendᴿ
    (structural-world-extendᴿ plan)
structural-world-extendᴿ (structural-bind ins follows plan) =
  composeWorldExtendᴿ
    (target-insert-bind-world-extendᴿ ins follows)
    (structural-world-extendᴿ plan)
