module strong.notes.ColorVsClosed where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open Ctxᵗ

-- the witness's three contexts
Γᵢ Γₑ Δ : Ctxᵗ
Γᵢ = bind ∷ [] ∥ []                        -- the boundary's interior
Γₑ = bind ∷ asgn (lvl zero) ∷ [] ∥ []      -- its exterior
Δ  = asgn (lvl zero) ∷ [] ∥ []             -- the redex's context

A : Ty
A = ` zero

-- COLOUR AGREES between the redex's context and the interior …
colour : length (stk Δ) ≡ length (stk Γᵢ)
colour = refl

-- … and so, therefore, does well-formedness of the type argument.
wfΔ : Δ ⊢ᵗ A
wfΔ = wf-var t-here

wfΓᵢ : Γᵢ ⊢ᵗ A
wfΓᵢ = wf-var t-here

-- but `` ` 0 `` DENOTES different addresses on the two sides: the
-- assignment out here, the ∀'s binder in there.
denΔ : Δ ∋n zero := lvl zero
denΔ = n-here-asgn

denΓᵢ : ∀ {α} → ¬ (Γᵢ ∋n zero := α)
denΓᵢ ()

-- and the two QUOTES disagree: outside, `` ` 0 `` is the level; inside
-- it is the ∀'s bound variable.
qΔ : [] ∣ Δ ⊢⌊ A ⌋ `ᵃ (lvl zero)
qΔ = quote-var n-here-asgn

qΓᵢ : [] ∣ Γᵢ ⊢⌊ A ⌋ `ᵛ zero
qΓᵢ = quote-bv b-here
