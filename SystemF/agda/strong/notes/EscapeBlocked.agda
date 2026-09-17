module strong.notes.EscapeBlocked where

-- IS THE ESCAPE REACHABLE?  `after-add`'s only exit is an `unseal`
-- firing while the running type is a variable.  Three facts, and
-- together they say the exit can only ever be adjacent to the seal that
-- opened it — where `fuse` closes it.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion

------------------------------------------------------------------------
-- (1)  WHICH ADDRESS an unseal must be at
------------------------------------------------------------------------
-- A name determines its address.  So if the running type is `` ` r ``
-- and the frame names β by r, an `unseal X δ` fires only when its own
-- abstract side is `` ` r `` — `Ξ ∋n r := δ` — and then δ ≡ β.  An
-- unseal exits ONLY AT THE ADDRESS THE RUNNING VARIABLE NAMES.

name-det : ∀ {Γ X α β} → Γ ∋n X := α → Γ ∋n X := β → α ≡ β
name-det n-here-asgn n-here-asgn = refl
name-det (n-skip-asgn p) (n-skip-asgn q) = name-det p q
name-det (n-skip-bind p) (n-skip-bind q) = name-det p q

------------------------------------------------------------------------
-- (2)  AN INTERVENING CROSSING CANNOT BE AT THAT ADDRESS
------------------------------------------------------------------------
-- Every `hide`/`show` carries `NotAssigned` on the side WITHOUT the
-- assignment, and β is assigned there — the seal that made the running
-- type a variable put it on the stack, and nothing has popped it.  So
-- an intervening crossing is at a DIFFERENT address, and by (1) it can
-- never be the one that exits.

fresh-≢ : ∀ {Γ α β Y} → NotAssigned Γ α → Γ ∋n Y := β → ¬ (α ≡ β)
fresh-≢ na p refl = na p

------------------------------------------------------------------------
-- (3)  SO THE EXIT IS ADJACENT TO ITS SEAL — AND THERE IT FUSES
------------------------------------------------------------------------

fuses : ∀ X β → fuse (seal X β) (unseal X β) ≡ just []
fuses X β with X ≟ X
fuses X β | yes _ = refl
fuses X β | no ne = ⊥-elim (ne refl)

------------------------------------------------------------------------
-- WHAT REMAINS
------------------------------------------------------------------------
-- (1)–(3) are the three steps; what is not yet formal is the induction
-- carrying β's assignment along.  The invariant `after-add` wants is
--
--   the running type is `` ` r ``, `Ξ ∋n r := β`, and β IS ASSIGNED in
--   the current context
--
-- which a `seal` at β establishes, a `hide`/`show` preserves (their
-- types are unchanged, and by (2) they sit at other addresses, so they
-- push and pop ABOVE β), and only an `unseal` at β can end — which by
-- (2) means no crossing intervenes, so it is adjacent to the seal and
-- (3) applies.
--
-- NOTE WHAT IS NOT NEEDED: no premise on `hide`/`show`.  So `arr`'s
-- dualization is untouched and M₅ stays typable.  The old proof used
-- the SHIFT for this; the new one uses `NameFn Ξ`, which the boundary
-- already carries.
