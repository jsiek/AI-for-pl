module DynamicGradualGuarantee where

-- File Charter:
--   * THE STATEMENT OF GTNF's DYNAMIC GRADUAL GUARANTEE, for the cast
--     calculus (proof/DGG/PLAN.md §2; approved by Jeremy, 2026-10-02).
--     Closed programs at the empty context, related at the initial
--     world `∅ʷ`; the LEFT term is the more precise one.  The four
--     parts are GTLC's (GTLC/agda/proof/DynamicGradualGuarantee.agda),
--     with the sides flipped to GTNF's orientation.
--   * TYPES DO NOT CHANGE ALONG A RUN: GTNF's types are name-indexed and
--     an allocation renames only rep. vars, so the final values are
--     related at the original types `A ⊑ A′`, at some well-formed world
--     over the two runs' final contexts (`runCtx`).
--   * STATEMENT ONLY.  The proof is proof/DGG/DynamicGradualGuarantee*;
--     when it is finished, this module gains the thin wrapper
--     `dgg : DGG`.  Deferred: the source-level guarantee, a corollary
--     through `compile-⊑` once GTNF has a source language.

open import Data.List using ([])
open import Data.Product using (Σ-syntax; ∃-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty)
open import Ctx using (empty)
open import Coercion using (Label)
open import Terms using (Term; Value; blame)
open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; runCtx)
open import ImprecisionWorld using (World; ∅ʷ; WfWorld; _⊑ᵂ⟨_⟩_)
open import TermImprecision using (_∣_⊢_⊑_∶_)

------------------------------------------------------------------------
-- Observations of closed runs
------------------------------------------------------------------------

-- a run from the empty context ends in a value or in blame
Converges : Term → Set
Converges M =
  ∃[ N ] Σ[ r ∈ empty ⊢ M -→* N ] (Value N ⊎ (∃[ ℓ ] (N ≡ blame ℓ)))

Diverges : Term → Set
Diverges M = ¬ Converges M

-- every state the run reaches is blame or takes another step
DivergeOrBlame : Term → Set
DivergeOrBlame M =
  ∀ {N} (r : empty ⊢ M -→* N)
  → (∃[ ℓ ] (N ≡ blame ℓ)) ⊎ (∃[ N′ ] ∃[ ξ ] (runCtx r ⊢ N -→ N′ ∣ ξ))

-- two final values related at the original types, at some well-formed
-- world over the two runs' final contexts
RelatedValues : ∀ {M M′ V V′} (A A′ : Ty)
  → empty ⊢ M -→* V → empty ⊢ M′ -→* V′ → Set
RelatedValues {V = V} {V′} A A′ r r′ =
  Σ[ W ∈ World (runCtx r) (runCtx r′) ] WfWorld W
    × Σ[ q ∈ A ⊑ᵂ⟨ W ⟩ A′ ] (W ∣ [] ⊢ V ⊑ V′ ∶ q)

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

DGG : Set
DGG = ∀ {M M′ A A′} {p : A ⊑ᵂ⟨ ∅ʷ ⟩ A′}
  → ∅ʷ ∣ [] ⊢ M ⊑ M′ ∶ p
    -- 1. if the more precise side reaches a value, the less precise
    --    side reaches a related value
  → (∀ {V} (r : empty ⊢ M -→* V) → Value V
     → ∃[ V′ ] Σ[ r′ ∈ empty ⊢ M′ -→* V′ ]
         (Value V′ × RelatedValues A A′ r r′))
    -- 2. if the more precise side diverges, so does the less precise
  × (Diverges M → Diverges M′)
    -- 3. if the less precise side reaches a value, the more precise
    --    side reaches a related value or blame
  × (∀ {V′} (r′ : empty ⊢ M′ -→* V′) → Value V′
     → (∃[ V ] Σ[ r ∈ empty ⊢ M -→* V ]
          (Value V × RelatedValues A A′ r r′))
       ⊎ (∃[ ℓ ] (empty ⊢ M -→* blame ℓ)))
    -- 4. if the less precise side diverges, the more precise side
    --    diverges or blames
  × (Diverges M′ → DivergeOrBlame M)
