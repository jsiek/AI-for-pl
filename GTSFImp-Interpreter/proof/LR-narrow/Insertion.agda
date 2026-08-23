module proof.LR-narrow.Insertion where

-- File Charter:
--   * Proves reindexing of the open compiled-term relation along equalities
--     of endpoint types, contexts, and terms.
--   * Uses uniqueness of type imprecision derivations for the index.

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import CastTerms using (Term)
import proof.DGG.CtxImp as CTI
import proof.Imprecision as PI
open import LR-narrow.World
open import LR-narrow.TermRelation

compiled-term-relation-reindex : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴾ′ Aᴵ Aᴵ′}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ Γ′ : CTI.CtxImp (forgetWorld W)}
    {Mᴾ Mᴾ′ : Term Δᴾ} {Mᴵ Mᴵ′ : Term Δᴵ}
    (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
    (q : Aᴾ′ ⊑ᵂ⟨ core W ⟩ Aᴵ′)
  → Aᴾ ≡ Aᴾ′
  → Aᴵ ≡ Aᴵ′
  → Γ ≡ Γ′
  → Mᴾ ≡ Mᴾ′
  → Mᴵ ≡ Mᴵ′
  → CompiledTermRelation {W = W} p k Γ Mᴾ Mᴵ
  → CompiledTermRelation {W = W} q k Γ′ Mᴾ′ Mᴵ′
compiled-term-relation-reindex p q refl refl refl refl refl related
  rewrite PI.⊑-unique p q = related
