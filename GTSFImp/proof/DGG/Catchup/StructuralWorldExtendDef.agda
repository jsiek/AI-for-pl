module proof.DGG.Catchup.StructuralWorldExtendDef where

-- File Charter:
--   * Records the keep/bind insertion history of a right-world extension.
--   * Retains center insertion evidence needed by source-wrapper recursion.

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Maybe using (Maybe)

open import Types using (Ty; TyVar)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import Reduction using
  (StoreChanges; []; _∷_; keep; bind; applyStores)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.TargetExtend as TE
open CTI2 using (World)


data StructuralWorldExtendᴿ {Δᴸ} :
    ∀ {Δᴿ Δᴿ′ Δ Δ′}
    → StoreChanges Δᴿ Δᴿ′
    → World Δᴸ Δᴿ Δ
    → World Δᴸ Δᴿ′ Δ′
    → Set₁ where

  structural-[] : ∀ {Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    → StructuralWorldExtendᴿ [] W W

  structural-keep : ∀ {Δᴿ Δᴿ′ Δ Δ′}
      {χs : StoreChanges Δᴿ Δᴿ′}
      {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    → StructuralWorldExtendᴿ χs W W′
    → StructuralWorldExtendᴿ (keep ∷ χs) W W′

  structural-bind : ∀ {Δᴿ Δᴿ′ Δ Δ₁ Δ′}
      {B : Ty Δᴿ} {π : Δ ↪ᵗ Δ₁}
      {χs : StoreChanges (suc Δᴿ) Δᴿ′}
      {W : World Δᴸ Δᴿ Δ}
      {W₁ : World Δᴸ (suc Δᴿ) Δ₁}
      {W′ : World Δᴸ Δᴿ′ Δ′}
    → TE.TargetInsert wk↪ᵗ π W W₁
    → CTI2.targetStoreʷ W₁ ≡
        applyStores (bind B ∷ []) (CTI2.targetStoreʷ W)
    → StructuralWorldExtendᴿ χs W₁ W′
    → StructuralWorldExtendᴿ (bind B ∷ χs) W W′


record StructuralRebaseAtᴸResult {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
    (plan : StructuralWorldExtendᴿ χs W W′)
    {Wᵖ : World Δᴸ Δᴿ Δ} {Xᴸ? : Maybe (TyVar Δᴸ)}
    (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?) : Set₁ where
  field
    Wᵖ′ : World Δᴸ Δᴿ′ Δ′
    premise-plan : StructuralWorldExtendᴿ χs Wᵖ Wᵖ′
    post-rebase : CTI2.RebaseAtᴸ W′ Wᵖ′ Xᴸ?
    post-mono : CTI2.ImpEnvMono W Wᵖ → CTI2.ImpEnvMono W′ Wᵖ′
