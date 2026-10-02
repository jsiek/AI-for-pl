module notes.LeftOnlyUnbindProbe where

-- File Charter:
--   * REGRESSION PROBE for design.md §12.5, question 3.  The former
--     left program tried to cast the polymorphic identity through
--       gen X. inst Y. ((X! ; Y?ℓ) → (Y! ; X?ℓ)).
--     D20 removes both tag-then-check sequences from coercion syntax.
--   * `no-X-to-Y` records the semantic reason: evidence-shaped coercions
--     cannot mediate directly between two distinct names.  Thus this
--     proposed left-only unbind example is outside GTNF, while the
--     structural right program remains typed.

open import Data.List using ([]; _∷_)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx using (Ctxᵗ; empty; underΛ)
open import Coercion
open import Terms
open import Conversion
open import examples.TypeCheck using (tc)
open import proof.TypeSafety.CoercionTyping using (coercion-var-to-var)

ΔX ΔXY : Ctxᵗ
ΔX = underΛ empty
ΔXY = underΛ ΔX

no-X-to-Y : ∀ {p}
  → ¬ (ΔXY ∣ X∼★ ∷ ★∼X ∷ [] ⊢ᵖ p ∶ ` 1 ⟹ ` 0)
no-X-to-Y ⊢p with coercion-var-to-var ⊢p
no-X-to-Y ⊢p | ()

I : Term
I = Λ (ƛ (` 0) ∙ ` 0)

struct : Coercion
struct = ∀ᵖ (idᵖ (` 0) ↦ᵖ idᵖ (` 0))

use : Coercion → Term
use p = (ƛ (`∀ (` 0 ⇒ ` 0)) ∙
          ((ν `ℕ · ` 0 ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · $ 5))
        · (I ⟨ [] ∣ p ⟩)

Q-R : Term
Q-R = use struct

Q-R-⊢ : empty ∣ [] ⊢ Q-R ⦂ `ℕ
Q-R-⊢ = tc
