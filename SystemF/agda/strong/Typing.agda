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

open import Data.Nat using (ℕ; zero; suc; s≤s; z≤n)
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

------------------------------------------------------------------------
-- Grounding examples for the (conceal) rule
------------------------------------------------------------------------

private
  -- context  Y:=ℕ   (Y at type-index 0)
  Δ✓ : TCtx
  Δ✓ = rvld `ℕ ∷ []

  -- From notes Example 1:  7↓[Y:=ℕ]@Y : Y   (a constant sealed at Y).
  -- ∋ recovers A = ℕ; the body 7 is checked at Y[Y:=ℕ] = ℕ, with Y concealed.
  _ : Δ✓ ∣ [] ⊢ ($ 7) ↓[ 0 , `ℕ , ` 0 ] ⦂ ` 0
  _ = ⊢↓ here (new wf-ℕ) (wf-var here-rvld) ⊢$

  -- A sealed function  (λn:ℕ.n)↓[X:=ℕ]@(X→X) : X→X   (as f in Example 2).
  -- B = X→X is well-formed (X revealed); body checked at (X→X)[X:=ℕ] = ℕ→ℕ,
  -- and its own λ rebuilds a fresh term context from [].
  _ : Δ✓ ∣ [] ⊢ (ƛ `ℕ ∙ ` 0) ↓[ 0 , `ℕ , (` 0 ⇒ ` 0) ] ⦂ (` 0 ⇒ ` 0)
  _ = ⊢↓ here (new wf-ℕ) (wf-⇒ (wf-var here-rvld) (wf-var here-rvld))
          (⊢ƛ wf-ℕ (⊢` here))

  -- Example 5, the WrapConceal reduct (line 232):
  --   ((λg:ℕ→ℕ. g·42) · (λx:X.x)↑[X:=ℕ]) ↓[X:=ℕ]@X  :  X
  -- Concealment over a NON-value body that re-reveals X fresh inside the seal.
  -- The outer conceal blocks X (index 0); the inner ↑ binds a fresh X, and
  -- λx:X.x uses THAT one — so both live together without conflict.
  _ : (rvld `ℕ ∷ []) ∣ [] ⊢
        ((ƛ (`ℕ ⇒ `ℕ) ∙ (` 0 · $ 42)) · ((ƛ ` 0 ∙ ` 0) ↑[ `ℕ , (` 0 ⇒ ` 0) ]))
          ↓[ 0 , `ℕ , ` 0 ]
        ⦂ ` 0
  _ = ⊢↓ here (new wf-ℕ) (wf-var here-rvld)
          (⊢· (⊢ƛ (wf-⇒ wf-ℕ wf-ℕ) (⊢· (⊢` here) ⊢$))
              (⊢↑ (⊢ƛ (wf-var here-rvld) (⊢` here)) wf-ℕ))

  -- context  X:=ℕ, Y:=(X→X)   (Y at index 0, its rep X→X mentions X; X at index 1)
  Δ₆ : TCtx
  Δ₆ = rvld (` 0 ⇒ ` 0) ∷ rvld `ℕ ∷ []

  -- Example 6 (line 250):  5↓[X:=ℕ]@ℕ  concealing X at INDEX 1, with the other
  -- revealed variable Y carrying a representation that mentions the concealed X.
  -- Stresses the representation lookup (a skip-rvld shift) in the Y:=(X→X) context.
  _ : Δ₆ ∣ [] ⊢ ($ 5) ↓[ 1 , `ℕ , `ℕ ] ⦂ `ℕ
  _ = ⊢↓ (skip-rvld here) (·rvld (new wf-ℕ)) wf-ℕ ⊢$

  -- Variant with annotation B = X (not ℕ), to exercise single-at at index 1:
  --   X[X:=ℕ] = ℕ, with X mentioned at index 1.
  _ : Δ₆ ∣ [] ⊢ ($ 5) ↓[ 1 , `ℕ , ` 1 ] ⦂ ` 1
  _ = ⊢↓ (skip-rvld here) (·rvld (new wf-ℕ)) (wf-var (skip-rvld here-rvld)) ⊢$

  -- Example 1's nested conceal (line 183):  3↓[Y:=ℕ]↓[X:=Y] : X   in context
  --   X:=Y, Y:=ℕ   (X at index 0 with rep Y; Y at index 1 with rep ℕ).
  -- The OUTER conceal has a non-closed representation A = Y, and the INNER
  -- conceal's lookup for Y skips the outer X-marker (skip-cncl in ∋ :=).
  _ : (rvld (` 0) ∷ rvld `ℕ ∷ []) ∣ [] ⊢
        ($ 3) ↓[ 1 , `ℕ , ` 1 ] ↓[ 0 , ` 1 , ` 0 ] ⦂ ` 0
  _ = ⊢↓ here (new (wf-var here-rvld)) (wf-var here-rvld)
          (⊢↓ (skip-cncl (λ ()) (skip-rvld here))
              (·cncl (s≤s z≤n) (·rvld (new wf-ℕ)))
              (wf-var (skip-cncl (λ ()) (skip-rvld here-rvld)))
              ⊢$)

  -- Requested check: in EVERY conceal instance above, the representation A is
  -- well-formed in the conceal's context Δ.
  --   examples 1,2 and Example 5 (context Δ✓): A = ℕ
  _ : Δ✓ ⊢ `ℕ
  _ = wf-ℕ
  --   Example 6 and its variant (context Δ₆): A = ℕ
  _ : Δ₆ ⊢ `ℕ
  _ = wf-ℕ
  --   Example 1 nested conceal, the two representations:
  _ : (rvld (` 0) ∷ rvld `ℕ ∷ []) ⊢ ` 1                 -- outer: A = Y (non-closed) ✓
  _ = wf-var (skip-rvld here-rvld)
  _ : (cncl 0 ∷ rvld (` 0) ∷ rvld `ℕ ∷ []) ⊢ `ℕ         -- inner: A = ℕ (looked up past ↓X)
  _ = wf-ℕ

  -- The Commute redex from Reduction.agda is a well-typed runtime term:
  --   (λx:X.x) ↓[Y:=ℕ]@(X→X) ↑[X:=ℕ]@(X→X)  :  ℕ→ℕ   at context  Y:=ℕ.
  -- (A *vacuous* seal: the annotation X→X does not mention the sealed Y.)
  _ : (rvld `ℕ ∷ []) ∣ [] ⊢
        ((ƛ ` 0 ∙ ` 0) ↓[ 1 , `ℕ , (` 0 ⇒ ` 0) ]) ↑[ `ℕ , (` 0 ⇒ ` 0) ]
        ⦂ (`ℕ ⇒ `ℕ)
  _ = ⊢↑ (⊢↓ (skip-rvld here)
              (·rvld (new wf-ℕ))
              (wf-⇒ (wf-var here-rvld) (wf-var here-rvld))
              (⊢ƛ (wf-var (skip-cncl (λ ()) here-rvld)) (⊢` here)))
         wf-ℕ
