module strong.Typing where

-- Strong System F — the term typing judgement  Δ ∣ Γ ⊢ M ⦂ A.
--
-- Two contexts: Δ the type context (strong.Context), Γ the term context.
-- The interesting rules are the three that move type variables:
--   ⊢Λ  extends Δ with an abstract variable and shifts Γ (⤊).
--   ⊢↑  (reveal) extends Δ with a FRESH revealed variable (index 0) and shifts
--       Γ; the result eliminates that variable, so it uses the index-0
--       substitution  B [ A ]ᵗ.
--   ⊢↓  (conceal) REFERS to an existing revealed variable X.  Its body is typed in
--       the PREFIX Δ ↓ X (X's existential scope) with the term context cleared.  The
--       representation A (from the shift-free lookup Δ ∋ X := A) is a type over that
--       prefix, and the body's type is the index-0 substitution B [ A ]ᵗ — exactly
--       dual to ⊢↑.  The annotation B lives in the X-at-0 frame rvld A ∷ (Δ ↓ X);
--       the result type is B relocated to the ambient Δ, i.e. shifted up by X.

open import Data.Nat using (ℕ; _+_)
open import Data.List using (List; []; _∷_)
open import strong.Types
open import strong.Context
open import strong.Terms

-- Δ, Γ, A, B, C, X, x are generalizable variables re-exported from Context.
private
  variable
    L M N : Term
    n : ℕ

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
     → (rvld A ∷ (Δ ↓ X)) ⊢ B
     → (Δ ↓ X) ∣ [] ⊢ M ⦂ B [ A ]ᵗ
       ---------------------------------------------
     → Δ ∣ Γ ⊢ M ↓[ X , A , B ] ⦂ renameᵗ (X +_) B
