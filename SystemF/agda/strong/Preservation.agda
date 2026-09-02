module strong.Preservation where

-- Type preservation for Strong System F.
--
-- PROOF TEMPLATE (in progress): induction on the reduction M -→ M′, inverting
-- the typing of M in each case.  The statement carries ⊢ Δ (the type context is
-- well-formed), needed by the computation cases to recover representation
-- well-formedness (∋:=-⊢).  The ξ congruence cases are filled with the induction
-- hypothesis; the computation cases are holes to be filled one by one.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import strong.Types
open import strong.Context
open import strong.Weakening
open import strong.Terms
open import strong.Typing
open import strong.Reduction

-- Δ, Γ, A, B, C, X, n are generalizable variables re-exported from Context.
private
  variable
    L M M′ N V W F : Term

preservation : ⊢ Δ → M -→ M′ → Δ ∣ Γ ⊢ M ⦂ A → Δ ∣ Γ ⊢ M′ ⦂ A

------------------------------------------------------------------------
-- Computation rules
------------------------------------------------------------------------

-- TyBeta:  (ΛX.V) @B[A]  →  V ↑[X:=A]@B
preservation ⊢Δ (β-Λ v)          (⊢·[] (⊢Λ ⊢V) ⊢A)        = {!!}

-- Beta:  (λx:A.N) · W  →  N[x:=W]
preservation ⊢Δ (β-ƛ v)          (⊢· (⊢ƛ wfA ⊢N) ⊢W)      = {!!}

-- WrapReveal
preservation ⊢Δ (β-↑ g v)        (⊢· (⊢↑ ⊢F ⊢A) ⊢W)       = {!!}

-- RevealCnst:  k ↑[X:=A]@B  →  k
preservation ⊢Δ β-$↑             (⊢↑ ⊢$ ⊢A)               = ⊢$

-- WrapConceal
preservation ⊢Δ (β-↓· vF vW)     (⊢· (⊢↓ ∋X wfB ⊢F) ⊢W)   = {!!}

-- Cancel:  V↓[X:=A]@B ↑[X:=A]@B  →  V
preservation ⊢Δ (β-cancel v)     (⊢↑ (⊢↓ ∋X wfB ⊢V) ⊢A)   = {!!}

-- Drop:  V↓[Y:=B]@C ↑[X:=A]@D  →  V↓[Y:=B]@C
preservation ⊢Δ (β-drop v _ _ _) (⊢↑ (⊢↓ ∋X wfB ⊢V) ⊢A)   = {!!}

-- TyWrapRevl
preservation ⊢Δ (β-↑[] g)        (⊢·[] (⊢↑ ⊢F ⊢A) ⊢C)     = {!!}

-- TyWrapCncl
preservation ⊢Δ (β-↓[] vF)       (⊢·[] (⊢↓ ∋X wfB ⊢F) ⊢C) = {!!}

------------------------------------------------------------------------
-- ξ congruence rules  (induction hypothesis)
------------------------------------------------------------------------

preservation ⊢Δ (ξ-·-l r)   (⊢· ⊢L ⊢M)     = ⊢· (preservation ⊢Δ r ⊢L) ⊢M
preservation ⊢Δ (ξ-·-r v r) (⊢· ⊢L ⊢M)     = ⊢· ⊢L (preservation ⊢Δ r ⊢M)
preservation ⊢Δ (ξ-↑ r)     (⊢↑ ⊢M ⊢A)     = ⊢↑ (preservation (⊢rvld ⊢Δ ⊢A) r ⊢M) ⊢A
preservation ⊢Δ (ξ-↓ r)     (⊢↓ ∋X wfB ⊢M) =
  ⊢↓ ∋X wfB (preservation (⊢cncl ⊢Δ (∋:=→∋tv ∋X)) r ⊢M)
preservation ⊢Δ (ξ-·[] r)   (⊢·[] ⊢L ⊢A)   = ⊢·[] (preservation ⊢Δ r ⊢L) ⊢A
preservation ⊢Δ (ξ-Λ r)     (⊢Λ ⊢M)        = ⊢Λ (preservation (⊢abst ⊢Δ) r ⊢M)
