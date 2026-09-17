module strong.notes.HideUnseal where

-- THE STAGE-3 PROBLEM, on one conversion.
--
-- `proof.ConvCanonicity.after-add` says: once an element has ADDED a
-- crossing assignment and the running type is a variable, the rest of a
-- normal-form conversion leaves it a variable.  `Progress` uses that
-- (via `canonicity`) to know a value's conversion has a determinate
-- shape.
--
-- Under the frame the lemma is FALSE, and this is the whole of it.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion

Sg : Store
Sg = `𝔹ᴿ ∷ []          -- one address, `lvl 0`, whose representation is 𝔹

-- the three contexts the spine passes through, and the FRAME
Γ₁ Γ₂ Γ₃ Ξ : Ctxᵗ
Γ₁ = [] ∥ []                          -- interior: α is anonymous
Γ₂ = asgn (lvl zero) ∷ [] ∥ []        -- between: α is named
Γ₃ = [] ∥ []                          -- exterior: anonymous again
Ξ  = asgn (lvl zero) ∷ [] ∥ []        -- the frame keeps the name

c : Conv
c = hide zero (lvl zero) ∷ᶜ unseal zero (lvl zero) ∷ᶜ id `𝔹

-- it is a NORMAL FORM: `fuse (hide X α) (unseal X α)` has no row
nf-c : NF c
nf-c = nf-cons nf-hide (nf-cons nf-unseal nf-id irr-id) (irr-cons refl)

-- … and under the FRAME rules it is WELL TYPED, from a VARIABLE to 𝔹
⊢c : Sg ∣ Ξ ∣ Γ₁ ⊢ c ∶ ` zero ⇝ `𝔹 ⊣ Γ₃
⊢c = conv-cons (conv-hide (a-lvl l-here) (wf-var t-here) pop-here (λ ()))
       (conv-cons (conv-unseal (r-lvl l-here) read-𝔹 n-here-asgn
                     pop-here (λ ()))
         (conv-id wf-𝔹))

-- WHY IT USED TO BE IMPOSSIBLE.  The old `conv-hide` re-spelled its
-- type — `A ⇝ renameᵗ (shiftAtᵗ X) A` — and `shiftAtᵗ X` never produces
-- `` ` X ``, so the `unseal`'s source could not be what the `hide`
-- handed it.  That is `shiftAt-var-≢`, and it is the argument the
-- `unseal`-after-`hide` case of `after-add` ran on.  With `hide` now
-- `A ⇝ A` the argument is gone, and so is the fact.
shift-never-X : ∀ A → ¬ (renameᵗ (shiftAtᵗ zero) A ≡ ` zero)
shift-never-X (` Y) ()
shift-never-X `ℕ ()
shift-never-X `𝔹 ()
shift-never-X (A ⇒ B) ()
shift-never-X (`∀ A) ()

------------------------------------------------------------------------
-- THE LOST INFORMATION, and which form of it we want
------------------------------------------------------------------------
-- Jeremy: "an id conversion is never used at the type variable that is
-- being hidden or revealed (otherwise it would have been a seal or
-- unseal)" — so the premise goes on BOTH `conv-hide` and `conv-show`,
-- which are duals and must stay duals for `arr`.  notes-v8.md says it too, of `id{+X:=α}`: "the type must
-- not mention `X`".  The old `shiftAtᵗ` encoded it — a shifted type
-- cannot mention the slot shifted into — and with the shift gone it
-- has to be a premise.  Two readings, and they DISAGREE:
--
--   (A)  the type is not THE hidden variable          A ≢ ` X′
--   (B)  the hidden variable does not OCCUR in it     X′ ∉ A
--
-- where `X′` is the name the FRAME gives the hidden address.

-- the counterexample's hide, where the type IS the hidden variable
badA : Ty
badA = ` zero            -- and Ξ ∋n 0 := lvl 0

-- M₅'s hide, from notes/UnlockedFrame2's `W″`: its address is `lvl 0`,
-- the frame names it 0, and the type MENTIONS it — because the
-- boundary's own result type is `X → 𝔹`, and this is the outermost
-- crossing.
goodA : Ty
goodA = ` zero ⇒ `𝔹      -- and Ξ″ ∋n 0 := lvl 0

-- (A) separates them …
A-rejects-bad : ¬ (badA ≡ ` zero)  → ⊥
A-rejects-bad k = k refl

A-accepts-good : ¬ (goodA ≡ ` zero)
A-accepts-good ()

-- … and (B) does not: it throws M₅ out along with the counterexample.
B-rejects-good : occursᵗ zero goodA ≡ true
B-rejects-good = refl
