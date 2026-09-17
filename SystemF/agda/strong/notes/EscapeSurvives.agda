module strong.notes.EscapeSurvives where

-- BUILDING THE THIRD STATE FOUND A LONGER ESCAPE.
--
-- The restored `show`/`hide` row closes the ADJACENT case
--
--     seal{-X:=β} ∷ id{+X:=β} ∷ id{-X:=β} ∷ unseal{+X:=β}
--                    ^^^^^^^^^^^^^^^^^^^ these now fuse
--
-- but not this one, which puts a crossing at ANOTHER address in
-- between:
--
--     seal{-X:=β} ∷ id{+X:=β} ∷ id{-Y:=γ} ∷ id{-Z:=β} ∷ unseal{+Z:=β}
--
-- The seal pushes β and makes the running type a variable; the show
-- pops β; the hide at γ pushes γ; the hide at β pushes β BACK (legal —
-- β is unassigned by then); and the unseal pops β and exits.  Every
-- adjacency is irreducible.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.RepresentationTypes using (Addr; lvl)
open import strong.Conversion

-- the four adjacencies, at distinct addresses β = lvl 0, γ = lvl 1
a₁ : fuse (seal zero (lvl zero)) (show zero (lvl zero)) ≡ nothing
a₁ = refl

a₂ : fuse (show zero (lvl zero)) (hide zero (lvl (suc zero))) ≡ nothing
a₂ = refl                      -- the restored row needs BOTH to agree

a₃ : fuse (hide zero (lvl (suc zero))) (hide zero (lvl zero)) ≡ nothing
a₃ = refl

a₄ : fuse (hide zero (lvl zero)) (unseal zero (lvl zero)) ≡ nothing
a₄ = refl

-- WHAT THIS MEANS.  `fuse` is an ADJACENT-PAIR rewrite, and the escape
-- can always be padded with a crossing at another address, so no
-- finite set of rows can close it.  The invariant `after-add` wants —
-- "β is assigned here" — is genuinely destroyed by the `show` at β and
-- genuinely re-established by the later `hide` at β, with the two too
-- far apart for `fuse` to see.
--
-- So the third state does not rescue the induction, and the question
-- returns to the one it was hiding: after a `show` pops the running
-- variable's address, what stops it coming back?
