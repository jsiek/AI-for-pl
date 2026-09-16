module strong.notes.SubstAnnTest where

-- Strong System F v8 — AN EXAMPLE THAT ACTUALLY TESTS THE THREADING
-- (2026-09-16).
--
-- `Examples.inst-agrees` does not: there the spine is `show 1 α ∷ᶜ id …`
-- with slot 0 and `S = 𝔹`, so the step is `nameSub 1 0 = 0` (the slot
-- does not move) and `𝔹` is ground (nothing to shift).  Both threads
-- are no-ops, and the example passes under the OLD definition too.
--
-- To discriminate, the spine needs a crossing at a name that MOVES the
-- slot — `Y ≤ X` — and an annotation that mentions it.  `hide 0 α` is
-- the smallest such: going outward it inserts a name at 0, so the slot
-- moves 0 ↦ 1 and `S` shifts.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion

Σ₁ : Store
Σ₁ = `ℕᴿ ∷ []

-- interior: the `∀`'s binder alone.  exterior: the crossing on top of
-- it, so the slot sits at index 1 there.
Γᵢ Γₑ : Ctxᵗ
Γᵢ = bind ∷ [] ∥ []
Γₑ = asgn (lvl 0) ∷ bind ∷ [] ∥ []

c : Conv
c = hide 0 (lvl 0) ∷ᶜ id (` 1)

⊢c : Σ₁ ∣ Γᵢ ⊢ c ∶ ` 0 ⇝ ` 1 ⊣ Γₑ
⊢c = conv-cons (conv-hide (a-lvl l-here) (wf-var t-here) pop-here
                  (λ { (n-skip-bind ()) }))
       (conv-id (wf-var (t-there t-here)))

-- THE TERMINATOR'S `` ` 1 `` IS THE SLOT, read at the exterior.  The
-- threading sees that; the old definition, which kept the slot at 0,
-- did not — it read `` ` 1 `` as an ordinary variable and decremented
-- it to `` ` 0 ``, which at `Γₑ` is the CROSSING's name.
new : substAnn 0 `ℕ c ≡ hide 0 (lvl 0) ∷ᶜ id `ℕ
new = refl
