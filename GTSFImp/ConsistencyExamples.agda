module ConsistencyExamples where

-- File Charter:
--   * Catalogs derivations of consistency for a closed polymorphic type.
--   * Makes the constructor choices in each derivation explicit.

open import Data.Nat using (zero; suc)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans)

open import Types
open import Consistency

------------------------------------------------------------------------
-- (∀ X. ∀ Y. X ⇒ Y ⇒ X) ∼ (∀ X. ∀ Y. X ⇒ Y ⇒ X)
------------------------------------------------------------------------

-- This is the only constructor-distinct derivation.  Choosing inst or gen at
-- either quantifier leaves different variables at corresponding occurrences;
-- the variable consistency rule can only relate a variable to itself.
all-all :
  _∼_ {Δ = 0}
    (`∀ (`∀ (＇ 1 ⇒ ＇ 0 ⇒ ＇ 1)))
    (`∀ (`∀ (＇ 1 ⇒ ＇ 0 ⇒ ＇ 1)))
all-all =
  ∀ᶜ (∀ᶜ (id (＇ 1) ↦ id (＇ 0) ↦ id (＇ 1)))

------------------------------------------------------------------------
-- (∀ X. ∀ Y. X ⇒ X ⇒ Y) ∼ (∀ X. X ⇒ X ⇒ ★)
------------------------------------------------------------------------

-- This is the only constructor-distinct derivation.  The outer X binders
-- must be paired by ∀ᶜ, after which inst relates the remaining Y to ★.
instance
  Y∈X⇒X⇒Y-instance :
    _∈ᵗ_ {Δ = 2} 0 (＇ 1 ⇒ ＇ 1 ⇒ ＇ 0)
  Y∈X⇒X⇒Y-instance =
    ∈-fun-right (∉-var (≢→≢ᶠ (λ ())))
      (∈-fun-right (∉-var (≢→≢ᶠ (λ ()))) var-∈)

all-all∼all-star :
  _∼_ {Δ = 0}
    (`∀ (`∀ (＇ 1 ⇒ ＇ 1 ⇒ ＇ 0)))
    (`∀ (＇ 0 ⇒ ＇ 0 ⇒ ★))
all-all∼all-star =
  ∀ᶜ
    ((inst (id (＇ 1) ↦ id (＇ 1) ↦ (id (＇ 0) !))) (λ ()))

------------------------------------------------------------------------
-- (∀ X. ★ ⇒ X) ∼ ★
------------------------------------------------------------------------

-- The side conditions on inst and ∈-fun-right leave one derivation: inst
-- targets ★ ⇒ ★ and the occurrence premise selects the codomain X.

module XOccursRight where

  private
    instance
      X∈★⇒X-right-instance :
        _∈ᵗ_ {Δ = 1} 0 (★ ⇒ ＇ 0)
      X∈★⇒X-right-instance = ∈-fun-right ∉-star var-∈

  tag-after-inst :
    _∼_ {Δ = 0} (`∀ (★ ⇒ ＇ 0)) ★
  tag-after-inst =
    ((inst (id ★ ↦ (id (＇ 0) !))) (λ ())) !

------------------------------------------------------------------------
-- (∀ X. X) ∼ ★  and  ★ ∼ (∀ X. X)
------------------------------------------------------------------------

-- The universal ground `∀ X. ★` supplies a disjoint fallback.  The bridge
-- out of the empty universal has no reduction rule; the reverse bridge
-- eagerly blames.

all-var∼star : _∼_ {Δ = 0} (`∀ (＇ 0)) ★
all-var∼star = bot-elim !

star∼all-var : _∼_ {Δ = 0} ★ (`∀ (＇ 0))
star∼all-var = ？ bot-intro
