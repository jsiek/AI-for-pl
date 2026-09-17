module strong.notes.StuckSpine where

-- OPTION 5 MEASURED (2026-09-17): what does `Progress` demand?
--
-- With the `A ≢ ` X′` premise removed again, the question is whether a
-- conversion can reach a NON-variable target after an addition — that
-- is what `after-add` forbids and what `canonicity` spends.
--
-- FIRST FINDING: most of the shapes one would try are already blocked,
-- by the stack discipline and by the crossings' own freshness, so the
-- counterexample is much more specific than I expected.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ
open import strong.Conversion

Sg : Store
Sg = (`𝔹ᴿ ⇒ᴿ `𝔹ᴿ) ∷ []              -- α := 𝔹→𝔹

-- (1) `seal X α ∷ hide X α` is IMPOSSIBLE.  The seal's exterior has
--     `X:=α`, and that is the hide's interior — where `conv-hide`'s
--     `NotAssigned Γᵢ α` must hold.
seal-then-hide-⊥ : ¬ NotAssigned (asgn (lvl zero) ∷ [] ∥ []) (lvl zero)
seal-then-hide-⊥ na = na n-here-asgn

-- (2) A LATER element cannot reach past an intervening assignment
--     either: `▷` skips only `bind`s, never `asgn`s.
pop-past-asgn-⊥ : ∀ {Ss Bs Ss′ α β X}
  → ¬ ((asgn β ∷ asgn α ∷ Ss ∥ Bs) ▷ suc X := α ⇒ (Ss′ ∥ Bs))
pop-past-asgn-⊥ ()

-- SO THE ONLY SHAPE LEFT is the one `notes/HideUnseal` already found:
-- an `unseal` immediately after a `hide` AT THE SAME ADDRESS, with the
-- running type being the frame's name for that address.  The hide adds,
-- the unseal removes, `fuse` has no row for the pair, and the target is
-- the read-back — an arrow, if the address holds an arrow.
--
--   id{-X:=α} ∷ unseal{+X:=α} ∷ id (𝔹→𝔹)        :  ` X ⇝ 𝔹→𝔹
--
-- and `canonicity` cannot classify a value wrapped in a spine that
-- reaches it after a seal: `inert-var` wants a variable target,
-- `inert-arr`/`inert-all` want a view, and `arr⁻ (seal X α) = nothing`
-- makes a seal-bearing spine un-viewable.  That is what `Progress`
-- demands, and it is exactly what premise (A) delivered.
