module strong.notes.probes.V7DualScopeProbe where

-- PROBE (2026-09-13): `dual χ` does NOT return to the context χ left.
--
-- `Wrap` sends the argument back out through the boundary's dual scope:
--
--   νΘ,χ[V|c] · W  -→  νΘ,χ[ V · ν∅,-χ[W|c₁] | c₂ ]
--
-- For the inner boundary to type, `-χ` must lead from the interior Δᵢ back
-- to ΔΘ, because that is where `c₁` and the (weakened) argument live.  It
-- does not, in general: a CONCEAL removes a name IN PLACE, passing through
-- whatever anchors sit above it, while its dual REVEAL puts the name back
-- ON TOP.  The two contexts are observationally identical — same names,
-- same anchors, same anchor count — but they are different lists, and
-- `⊢ν` demands the literal context the scope judgment produces.
--
-- This is the shape of notes-v7 §14, where
--   χ = (-Y:=β) ; (-X:=α)  passes -X through the rep binding β.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.RepresentationTypes
open import strong.Ctx
open import strong.CtxMorph

-- The exterior: one abstract anchor, named X.
Δ₀ : Ctxᵗ
Δ₀ = name zero ∷ abst ∷ []

-- The boundary's store adds one representation binding on top.
ΔΘ : Ctxᵗ
ΔΘ = bind `ℕᴿ ∷ Δ₀

-- X's anchor is index 1 in ΔΘ (the store's binding took index 0).
χ : Scope
χ = conceal 1 ∷ []

-- Concealing X removes its name IN PLACE, under the store's binding.
Δᵢ : Ctxᵗ
Δᵢ = bind `ℕᴿ ∷ abst ∷ []

enter : ΔΘ ⊢χ χ ⇒ Δᵢ
enter = scope∷ (step-conceal (pop-bind pop-here)) scope[]

-- The dual reveals X again — but ON TOP of the store's binding.
Δ-back : Ctxᵗ
Δ-back = name 1 ∷ bind `ℕᴿ ∷ abst ∷ []

dual-χ : dual χ ≡ reveal 1 ∷ []
dual-χ = refl

leave : Δᵢ ⊢χ dual χ ⇒ Δ-back
leave = scope∷ (step-reveal (a-over-bind a-here-abst) unoccupied) scope[]
  where
  unoccupied : Unoccupied Δᵢ 1
  unoccupied X (β , n-over-bind (n-over-abst ()) , eq)

-- And that is NOT the context we started from.
not-back : ¬ (Δ-back ≡ ΔΘ)
not-back ()

------------------------------------------------------------------------
-- … though nothing OBSERVABLE differs
------------------------------------------------------------------------

-- Same anchor count, so levels agree.
same-count : anchorCount Δ-back ≡ anchorCount ΔΘ
same-count = refl

-- Same colour.
same-scope : scopeᵗ Δ-back ≡ scopeᵗ ΔΘ
same-scope = refl

-- X is source variable 0 naming anchor 1 in BOTH.
X-in-ΔΘ : ΔΘ ∋n zero := 1
X-in-ΔΘ = n-over-bind n-here

X-in-Δ-back : Δ-back ∋n zero := 1
X-in-Δ-back = n-here

-- And the store's representation reads the same in both.
rep-in-ΔΘ : ΔΘ ∋r zero := `ℕᴿ
rep-in-ΔΘ = r-here

rep-in-Δ-back : Δ-back ∋r zero := `ℕᴿ
rep-in-Δ-back = r-over-name r-here
