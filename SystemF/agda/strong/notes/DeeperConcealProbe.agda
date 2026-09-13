module strong.notes.DeeperConcealProbe where

-- IS THE "DEEPER CONCEAL OF Y" CASE REACHABLE?   (2026-09-11)
--
-- The question (notes-v6): a boundary that BOTH truncates at Z AND appends
-- Y:=A with A mentioning Z cannot store Y's representation in its interior
-- telescope — Y's prefix there is Γ↓Z, which lacks Z.  An ABSTRACT entry
-- would do, UNLESS something INSIDE needs Y's representation.
--
-- The shape that needs it is a nested boundary whose conversion mentions
-- Y.  In v6 that is precisely AppBnd's DUAL: applying the value crosses
-- the argument back out through a conceal of Y, carrying `-Y`.
--
-- THIS PROBE SHOWS THE SHAPE IS REACHED, in three steps, by a closed
-- program — worked in the LIVE v3 calculus, where the corresponding node
-- is `ν conceal (0 ∷ []) [ … ]` nested inside `ν intro (` 0) [ … ]`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong.Types
open import strong.Ctx
open import strong.Conversion
open import strong.CtxMorph
open import strong.Terms
open import strong.TermSubst
open import strong.Reduction

------------------------------------------------------------------------
-- 1.  THE PROGRAM
------------------------------------------------------------------------

--   (λg:(∀Y. ℕ→ℕ). ΛZ. (g •(ℕ→ℕ)[Z]) · 5) · (ΛY. λw:ℕ. w)
--
-- g is used at the type variable Z bound BETWEEN g's binder and the use,
-- so Beta must send it across the ΛZ — and the instantiation is AT the
-- concealed variable.  Then the result is applied, which is what drags a
-- conceal of the freshly introduced Y down inside the intro.

Δ₀ Δ₁ : Ctxᵗ
Δ₀ = []
Δ₁ = unmasked abst ∷ []          -- under the ΛZ

-- ΛY. λw:ℕ. w      : ∀Y. ℕ→ℕ
polyK : Term
polyK = Λ (ƛ `ℕ ∙ (` 0 ⟪ 0 ∷ [] ⟫) ⟪ 0 ∷ [] ⟫) ⟪ [] ⟫

-- ΛZ. (g •(ℕ→ℕ)[Z]) · 5
bodyΛ : Term
bodyΛ = Λ (((` 0 ⟪ 0 ∷ [] ⟫) • (`ℕ ⇒ `ℕ) [ ` 0 ]⟪ 0 ∷ [] ⟫)
             · ($ 5) ⟪ 0 ∷ [] ⟫) ⟪ [] ⟫

prog : Term
prog = (ƛ (`∀ (`ℕ ⇒ `ℕ)) ∙ bodyΛ ⟪ [] ⟫) · polyK ⟪ [] ⟫

------------------------------------------------------------------------
-- 2.  THE RUN
------------------------------------------------------------------------

V : Term                          -- λw:ℕ. w, the Λ's own body
V = ƛ `ℕ ∙ (` 0 ⟪ 0 ∷ [] ⟫) ⟪ 0 ∷ [] ⟫

-- STEP 1 — Beta.  crossΛ conceals Z from the image.
after₁ : Term
after₁ = Λ (((ν conceal (0 ∷ []) [ polyK ])
               • (`ℕ ⇒ `ℕ) [ ` 0 ]⟪ 0 ∷ [] ⟫)
             · ($ 5) ⟪ 0 ∷ [] ⟫) ⟪ [] ⟫

step₁ : Δ₀ ⊢ prog -→ after₁
step₁ = Beta (simple→value (SΛ (simple→value Sƛ)))

-- STEP 2 — TyConceal.  Instantiating AT the concealed Z mints the intro
-- whose representation IS that concealed variable.
after₂ : Term
after₂ = Λ ((ν intro (` 0)
               [ (ν conceal (1 ∷ []) [ V ]) ⟨ revTy 0 (`ℕ ⇒ `ℕ) ⟩ ])
             · ($ 5) ⟪ 0 ∷ [] ⟫) ⟪ [] ⟫

step₂ : Δ₀ ⊢ after₁ -→ after₂
step₂ = ξ-Λ (ξ-·-l (TyConceal ne (simple→value Sƛ)))

-- STEP 3 — AppBnd.  THE SHAPE.  The argument crosses the DUAL of the
-- intro, i.e. a CONCEAL OF THE FRESHLY INTRODUCED Y, nested INSIDE that
-- intro.
after₃ : Term
after₃ = Λ (ν intro (` 0)
              [ ((ν conceal (1 ∷ []) [ V ]) ⟨ revTy 0 (`ℕ ⇒ `ℕ) ⟩)
                  · (ν conceal (0 ∷ []) [ $ 5 ]) ⟪ 0 ∷ 1 ∷ [] ⟫ ]) ⟪ [] ⟫

step₃ : Δ₀ ⊢ after₂ -→ after₃
step₃ = ξ-Λ (AppBnd (Vp (Pintro (Pc (Cfun (Cn (Nc ne Sƛ)))))) (Vk const-$))

run : Δ₀ ⊢ prog -→* after₃
run = step₁ then step₂ then step₃ then done

------------------------------------------------------------------------
-- 3.  WHY THIS IS THE CASE IN QUESTION
------------------------------------------------------------------------

-- Read the frames of after₃, inside the ΛZ.
--
-- At the intro's interior: Y is slot 0, its REPRESENTATION IS Z (slot 1).
intro-interior : applyᵇ (intro (` 0)) Δ₁
  ≡ unmasked (bind (` 0)) ∷ unmasked abst ∷ []
intro-interior = refl

Y-rep-is-Z : (unmasked (bind (` 0)) ∷ unmasked abst ∷ []) ∋ 0 := (` 1)
Y-rep-is-Z = ez

-- And the nested node conceals SLOT 0 — that very Y.
dual-conceals-Y : dualᵇ (intro (` 0)) ≡ conceal (0 ∷ [])
dual-conceals-Y = refl

-- v3 SURVIVES THIS because masking RETAINS the binding: inside the nested
-- conceal, Y's entry is masked but still carries its representation.
v3-retains : lockχ (0 ∷ []) (applyᵇ (intro (` 0)) Δ₁)
  ≡ masked (bind (` 0)) ∷ unmasked abst ∷ []
v3-retains = refl

-- UNDER A PREFIX INTERIOR IT WOULD NOT.  v6 fuses the TyConceal step into
-- ONE boundary with Θ = (↓Z ; Y:=Z), whose interior is (Γ↓Z), Y — and Z
-- is GONE there.  Y's telescope entry therefore cannot carry its
-- representation, and the nested node is AppBnd's DUAL, whose conversion
-- is `-Y` and needs exactly that representation on its INTERIOR side.
--
-- So the case is REACHED, by a closed three-step program, and an abstract
-- entry does NOT suffice.  v6 needs either an anchored entry or v1's
-- fallback chain.
