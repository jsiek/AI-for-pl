module strong.Typing where

-- Strong System F — the term typing judgement  Δ ∣ Γ ⊢ M ⦂ A.
--
-- Two contexts: Δ the type context (strong.Context), Γ the term context.
-- The interesting rules are the three that move type variables:
--   ⊢Λ  extends Δ with an abstract variable and shifts Γ (⤊).
--   ⊢↑  (reveal) extends Δ with a FRESH revealed variable (index 0) and shifts
--       Γ; the result eliminates that variable, so it uses the index-0
--       substitution  B [ A ]ᵗ.
--   ⊢↓  (conceal) REFERS to an existing revealed variable X, blocks it for the
--       body (cncl X ∷ Δ) and clears the term context; the representation A is
--       recovered by the lookup  Δ ∋ X := A  scoped for that context, and the
--       body's type uses the general-index substitution  B [ X := A ]ᵗ.

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import strong.Types
open import strong.Context
open import strong.ConcealCtx
open import strong.Terms

-- Δ, Γ, A, B, C, X, x, n are generalizable variables re-exported from Context.
private
  variable
    L M N : Term

infix 3 _∣_⊢_⦂_
data _∣_⊢_⦂_ : TCtx → Ctx → Term → Ty → Set where

  ⊢` : Γ ∋ x ⦂ A
       ----------------
     → Δ ∣ Γ ⊢ ` x ⦂ A

  ⊢$ : ---------------
       Δ ∣ Γ ⊢ $ n ⦂ `ℕ

  ⊢ƛ : Δ ⊢ A
     → Δ ∣ A ∷ Γ ⊢ N ⦂ B
       ---------------------------
     → Δ ∣ Γ ⊢ ƛ A ∙ N ⦂ (A ⇒ B)

  ⊢· : Δ ∣ Γ ⊢ L ⦂ (A ⇒ B)
     → Δ ∣ Γ ⊢ M ⦂ A
       -------------------
     → Δ ∣ Γ ⊢ L · M ⦂ B

  ⊢Λ : (abst ∷ Δ) ∣ ⤊ Γ ⊢ N ⦂ C
       -------------------------
     → Δ ∣ Γ ⊢ Λ N ⦂ `∀ C

  ⊢·[] : Δ ∣ Γ ⊢ L ⦂ `∀ B
       → Δ ⊢ A
         ---------------------------------
       → Δ ∣ Γ ⊢ L ·[ B , A ] ⦂ B [ A ]ᵗ

  ⊢↑ : (rvld A ∷ Δ) ∣ ⤊ Γ ⊢ M ⦂ B
     → Δ ⊢ A
       ---------------------------------
     → Δ ∣ Γ ⊢ M ↑[ A , B ] ⦂ B [ A ]ᵗ

  ⊢↓ : Δ ∋ X := A
     → ConcealCtx Δ X
     → Δ ⊢ B
     → (cncl X ∷ Δ) ∣ [] ⊢ M ⦂ B [ X := A ]ᵗ
       -------------------------------------
     → Δ ∣ Γ ⊢ M ↓[ X , A , B ] ⦂ B
