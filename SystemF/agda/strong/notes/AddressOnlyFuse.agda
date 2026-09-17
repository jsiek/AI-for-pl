module strong.notes.AddressOnlyFuse where

-- SHOULD `fuse (show X α) (hide Y β)` TEST THE ADDRESS ONLY?
--
-- No — it needs both, and the reason is that the pair's two pops are
-- from DIFFERENT contexts, so the NAME is what says the assignment goes
-- back WHERE IT CAME FROM.
--
-- The show pops `X:=α` from its interior; the hide pushes `Y:=β` into
-- its exterior.  For the pair to be an identity the two contexts must
-- meet, i.e. `pushAsgn X α Γ ≡ pushAsgn Y β Γ` — which needs the
-- POSITION as well as the address, because `▷` counts binds.
--
-- Here is a pair at ONE address and TWO names, both halves well formed.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ

Γᵢ Γₑ Γₑ′ : Ctxᵗ
Γᵢ  = asgn (lvl zero) ∷ bind ∷ [] ∥ []     -- α at name 0
Γₑ  = bind ∷ [] ∥ []                       -- after the show
Γₑ′ = bind ∷ asgn (lvl zero) ∷ [] ∥ []     -- after the hide, at name 1

-- the show pops α at name 0 …
showPop : Γᵢ ▷ zero := lvl zero ⇒ Γₑ
showPop = pop-here

-- … and the hide pushes α back at name 1, which is equally legal
hidePop : Γₑ′ ▷ suc zero := lvl zero ⇒ Γₑ
hidePop = pop-bind pop-here

-- both freshness premises hold: after the show, α has NO name, because
-- name-uniqueness gave it only one
fresh : NotAssigned Γₑ (lvl zero)
fresh (n-skip-bind ())

-- BUT THE PAIR IS NOT AN IDENTITY — it moved the assignment past the
-- binder.  Cancelling it on the address alone would claim these are the
-- same context.
not-identity : ¬ (Γᵢ ≡ Γₑ′)
not-identity ()
