module notes.LeftOnlyUnbindProbe where

-- Probe (design.md §12.5, question 3): can a LEFT-ONLY unbind of a name
-- that both sides share arise?  The left casts the polymorphic identity
-- by a gen/inst detour through ★, the right by the structural ∀-cast;
-- both coercions have type ∀Y.Y→Y ⟹ ∀X.X→X.
-- NOTE: the left coercion is NOT the compilation of any consistency
-- evidence (design.md §12.5), so this pair is outside compile's image.

open import Data.List using ([])
open import Types
open import Ctx using (empty)
open import Coercion
open import Terms
open import Conversion
open import TypeCheck using (tc)
open import Eval

ℓ : Label
ℓ = 0

I : Term
I = Λ (ƛ (` 0) ∙ ` 0)

-- gen X. inst Y. ((X! ; Y?ℓ) → (Y! ; X?ℓ))
detour : Coercion
detour = genᵖ (instᵖ (((` 1) ! ︔ (` 0) ？ ℓ) ↦ᵖ ((` 0) ! ︔ (` 1) ？ ℓ)))

-- ∀X. (id(X) → id(X))
struct : Coercion
struct = ∀ᵖ (idᵖ (` 0) ↦ᵖ idᵖ (` 0))

use : Coercion → Term
use p = (ƛ (`∀ (` 0 ⇒ ` 0)) ∙ ((ν `ℕ · ` 0 ⟨ reveal 0 (` 0 ⇒ ` 0) ⟩) · $ 5))
        · (I ⟨ [] ∣ p ⟩)

Q-L Q-R : Term
Q-L = use detour
Q-R = use struct

Q-L-⊢ : empty ∣ [] ⊢ Q-L ⦂ `ℕ
Q-L-⊢ = tc

Q-R-⊢ : empty ∣ [] ⊢ Q-R ⦂ `ℕ
Q-R-⊢ = tc
