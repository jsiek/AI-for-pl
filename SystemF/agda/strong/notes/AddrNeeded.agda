module strong.notes.AddrNeeded where

-- Strong System F v8 — WHY `hide`/`show` CARRY AN ADDRESS, and hence
-- why a `Λ` must bind one.
--
-- A `Λ`'s address has no representation (`∋r` has no rule landing on a
-- bare `addr`), so a `Λ`'s variable can never be sealed or unsealed —
-- only hidden or shown.  So the whole question "can `Λ` stop binding
-- an address?" reduces to "do `hide`/`show` need one?".
--
-- They do.  Below is a well-typed conversion, in NORMAL FORM, that
-- RENAMES the assignment at name 0 from one address to another: the
-- `show` pushes `0 := lvl 0` going inward, the `hide` pops `0 := lvl 1`
-- going outward.  Strip the addresses and `fuse` would cancel the pair
-- on the name alone, collapsing this to `id ℕ` and silently changing
-- the exterior context.
--
-- The configuration is reachable, not merely well-formed: `Merge`
-- concatenates two boundaries, and the first's trailing `show` meets
-- the second's leading `hide` with the two addresses independent.
--
-- (`hide`-then-`show` is the opposite case and DOES force the two
-- addresses to agree, by `pop-unique` — both are pops from the same
-- context.  It is only the push-then-pop order that is free.)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.Conversion

-- two store levels, both ℕ
Σ₂ : Store
Σ₂ = `ℕᴿ ∷ `ℕᴿ ∷ []

-- a conversion that RENAMES the assignment at name 0, from lvl 0 to
-- lvl 1: `show` pushes one, `hide` pops the other
c : Conv
c = show 0 (lvl 0) ∷ᶜ hide 0 (lvl 1) ∷ᶜ id `ℕ

⊢c : Σ₂ ∣ (asgn (lvl 0) ∷ [] ∥ []) ⊢ c ∶ `ℕ ⇝ `ℕ ⊣ (asgn (lvl 1) ∷ [] ∥ [])
⊢c = conv-cons (conv-show (a-lvl l-here) wf-ℕ pop-here (λ ()))
       (conv-cons (conv-hide (a-lvl (l-there l-here)) wf-ℕ pop-here (λ ()))
         (conv-id wf-ℕ))

-- it is a NORMAL FORM: the two addresses differ, so the pair does not
-- fuse.  Drop the addresses and it would fuse away to `id ℕ` — which
-- would silently change the exterior context from lvl 1's assignment
-- to lvl 0's.
nf-c : NF c
nf-c = nf-cons nf-show (nf-cons nf-hide nf-id irr-id) (irr-cons refl)

no-fuse : fuse (show 0 (lvl 0)) (hide 0 (lvl 1)) ≡ nothing
no-fuse = refl

-- by contrast, at the SAME address the pair does cancel
yes-fuse : fuse (show 0 (lvl 0)) (hide 0 (lvl 0)) ≡ just []
yes-fuse = refl
