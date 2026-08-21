module proof.DGG.Inversion.SourceStripColumnView where

-- File Charter:
--   * Refutes the alias cycle exposed when an unmatched source seal sits
--     outside an independently tagged target seal column.
--   * Uses only store acyclicity, type imprecision, and the column's external
--     rebase geometry; it classifies no terms.
--   * Exposes the refutation used by `SourceStripWorkerProof`.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import TyStore using (_∋_⦂_)
open import Imprecision
import proof.DGG.CtxImp as CTX
import proof.DGG.SealPeelToolkit as SPT
open import proof.DGG.Inversion.TargetWalkSupport using
  (inner-source-pivot-eq; store-variable-distinct)

open CTX using
  (World; RebaseAt; _⊑ᵂ⟨_⟩_; sourceStoreʷ)

source-column-alias-cycle-⊥ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {R : Ty Δᴸ} {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → RebaseAt W′ W X Y
  → sourceStoreʷ W′ ∋ X ⦂ R
  → R ⊑ᵂ⟨ W′ ⟩ (＇ Y)
  → ⊥
source-column-alias-cycle-⊥ {W′ = W′} {Y = Y} {q = q}
    rb X∈ p
    with SPT.right-var-obligation-view {W = W′} {Y = Y} p
source-column-alias-cycle-⊥ {q = q} rb X∈ p
    | X₂ , refl , aligned
    with inner-source-pivot-eq rb q p
source-column-alias-cycle-⊥ rb X∈ p
    | X₂ , refl , aligned | refl =
  ⊥-elim (store-variable-distinct X∈ refl)
