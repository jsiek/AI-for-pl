module proof.TypeSafety.notes.InstCloseCounterexample where

-- File Charter:
--   * REGRESSION TEST for the preservation bug found in M1 (2026-10-02).
--     Before D20, general sequencing admitted the coercion
--       q = (Y?ℓ → id(ℕ)) ; (id(★) → ℕ!) ; (★→★)! ; X?ℓ
--         : (Y → ℕ) ⟹ X
--     under `Y:X∼★, X:★∼X`.  A surrounding `inst Y. q`, nested in the
--     domain of `inst X`, closed its target `X` to `★`, violating the
--     outer `NonStar` premise and refuting preservation.
--   * THE FIX is D20's evidence-shaped syntax.  The old `q` is no longer
--     a coercion term, and `q-has-no-typing` proves the stronger fact that
--     no evidence-shaped coercion can have its source and target typing.
--     Consequently the bad nested `inst` cannot be constructed.  Closing
--     preservation is proved in CoercionTyping.agda.

open import Data.Nat using (zero; suc)
open import Data.List using ([]; _∷_)
open import Relation.Nullary using (¬_)

open import Types
open import Ctx
open import Coercion
open import proof.TypeSafety.CoercionTyping
  using (nonstar-nonvar-to-var-impossible)

Δ₁ Δ₂ : Ctxᵗ
Δ₁ = underΛ empty
Δ₂ = underΛ Δ₁

-- Under Y (index 0) and X (index 1), this is exactly the typing that
-- the old four-stage `q` had.
q-has-no-typing : ∀ {q}
  → ¬ (Δ₂ ∣ X∼★ ∷ ★∼X ∷ []
          ⊢ᵖ q ∶ ` 0 ⇒ `ℕ ⟹ ` 1)
q-has-no-typing ⊢q =
  nonstar-nonvar-to-var-impossible ⊢q nv-⇒ ns-⇒
