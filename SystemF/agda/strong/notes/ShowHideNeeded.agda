module strong.notes.ShowHideNeeded where

-- BUILDING THE INDUCTION FOUND THE REAL CULPRIT.
--
-- The invariant is "the running type is `` ` r ``, `Ξ ∋n r := β`, and β
-- is ASSIGNED here".  A `seal` at β establishes it; `hide`/`show` at
-- other addresses preserve it.  The case that breaks is a `show` AT β:
-- it pops β, so β is no longer assigned, and the invariant is lost.
--
-- Can the escape then be reached?  Yes — like this:
--
--     seal{-X:=β} ∷ id{+X:=β} ∷ id{-X:=β} ∷ unseal{+X:=β} ∷ id B
--
-- the seal pushes β and makes the running type `` ` r ``; the show pops
-- it; the hide pushes it again — legal, because by then β IS unassigned,
-- which is exactly what `conv-hide`'s freshness asks; and the unseal
-- pops it and exits to the read-back.
--
-- AND IT IS A NORMAL FORM ONLY BECAUSE OF THIS MORNING'S DELETION.
-- `fuse (show X α) (hide Y β)` used to cancel; we removed the row
-- because nothing in the development needed it — measured against the
-- SHIFT-based rules, where `show ∷ hide` could not arise in this
-- position at all.  Under the frame it can.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List using ([])
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.RepresentationTypes using (Addr; lvl)
open import strong.Conversion

-- the row is back, so the escape's middle adjacency CANCELS
closed : ∀ X β → fuse (show X β) (hide X β) ≡ just []
closed X β with X ≟ X
closed X β | yes _ = refl
closed X β | no ne = ⊥-elim (ne refl)

still-blocked₁ : ∀ X β → fuse (seal X β) (show X β) ≡ nothing
still-blocked₁ X β = refl

still-blocked₂ : ∀ X β → fuse (hide X β) (unseal X β) ≡ nothing
still-blocked₂ X β = refl

-- Restoring the row closes it, and the row is SOUND: `show X β` pops β
-- and `hide X β` pushes it back, so the pair is net-zero on the context
-- AND type-preserving (both are `A ⇝ A` now).  The old `cancel-show`
-- proved exactly that, via `push-sound` on both pops — and it was
-- deleted with the row.
--
-- So the fix is not a premise, not `Inert`, not `arr`, not `substAnn`:
-- it is to PUT THE ROW BACK.  The deletion was justified by evidence
-- gathered under the old rules and is not justified under the new ones.
