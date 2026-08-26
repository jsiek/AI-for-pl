module LR-narrow.Insertion where

-- File Charter:
--   * Defines the insertion-generalized open relation and fundamental motive.
--   * A derivation at a syntactic world is tested at every semantic world
--     reached by a center insertion, on the renamed endpoint terms.
--   * Exposes reindexing of the open relation along propositional equalities
--     of endpoint types, terms, and contexts.
--   * Contains no compatibility proof.

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import CastTerms using (Term; renameᵗᵐ)
open import Consistency using (_↪ᵗ_; toRenameᵗ)
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import proof.DGG.WorldInsert
open import LR-narrow.World
open import LR-narrow.TermRelation
import proof.LR-narrow.Insertion as Proof

------------------------------------------------------------------------
-- Open relation below an insertion
------------------------------------------------------------------------

InsertedTermRelation : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
    {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
    (W : World Δᴾ′ Δᴵ′ Δᶜ′)
  → WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W)
  → (p : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Aᴵ)
  → ℕ
  → CTI.CtxImp Wᶜ
  → Term Δᴾ
  → Term Δᴵ
  → Set
InsertedTermRelation {ρᴾ = ρᴾ} {ρᴵ = ρᴵ} W ins p k Γ Mᴾ Mᴵ =
  CompiledTermRelation {W = W} (insert⊑ ins p) k (insertCtx ins Γ)
    (renameᵗᵐ ρᴾ Mᴾ) (renameᵗᵐ ρᴵ Mᴵ)

------------------------------------------------------------------------
-- Insertion-generalized fundamental motive
------------------------------------------------------------------------

record InsertedFundamentalProperty {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp Wᶜ}
    {Mᴾ : Term Δᴾ} {Mᴵ : Term Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨ Wᶜ ⟩ Aᴵ}
    (derivation : Wᶜ ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p) : Set where
  constructor inserted-proof
  field
    inserted-relation : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
        {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
        (W : World Δᴾ′ Δᴵ′ Δᶜ′)
        (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
      → ∀ k → InsertedTermRelation W ins p k Γ Mᴾ Mᴵ

open InsertedFundamentalProperty public

------------------------------------------------------------------------
-- Reindexing
------------------------------------------------------------------------

-- Type imprecision derivations are unique, so the open relation depends
-- on its derivation index only through the endpoint types.

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
compiled-term-relation-reindex = Proof.compiled-term-relation-reindex
