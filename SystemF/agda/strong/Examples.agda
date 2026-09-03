module strong.Examples where

-- Worked examples for Strong System F, clustered by program (numbered as in
-- notes.md).  For each program we give its typing derivation(s) and then its
-- reduction sequence.  All checks are anonymous; helper terms are private.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import strong.Types
open import strong.Context
open import strong.Terms
open import strong.Typing
open import strong.Reduction

------------------------------------------------------------------------
-- Example 1 — constants sealed at a variable (notes Example 1)
------------------------------------------------------------------------

-- typing:  7↓[Y:=ℕ]@Y : Y   at context  Y:=ℕ.
-- ∋ recovers A = ℕ; the body 7 is checked at Y[Y:=ℕ] = ℕ, with Y concealed.
_ : (rvld `ℕ ∷ []) ∣ [] ⊢ ($ 7) ↓[ 0 , `ℕ , ` 0 ] ⦂ ` 0
_ = ⊢↓ here (wf-var here-rvld) ⊢$

-- typing:  3↓[Y:=ℕ]↓[X:=Y] : X   at context  X:=Y, Y:=ℕ
-- (X at index 0 with rep Y; Y at index 1 with rep ℕ).  Under the prefix design a
-- conceal body is typed in the PREFIX Δ ↓ X: the outer conceal on X (index 0) has
-- body typed in Δ ↓ 0 = rvld ℕ ∷ [] (where Y is at index 0), so the inner conceal
-- there is on index 0 with rep ℕ — exactly Example 1a.  The outer conceal has a
-- non-closed representation A = Y (` 0, the shift-free rep stored at X).
_ : (rvld (` 0) ∷ rvld `ℕ ∷ []) ∣ [] ⊢
      ($ 3) ↓[ 0 , `ℕ , ` 0 ] ↓[ 0 , ` 0 , ` 0 ] ⦂ ` 0
_ = ⊢↓ here (wf-var here-rvld)
        (⊢↓ here (wf-var here-rvld) ⊢$)

-- the representations above are well formed in their PREFIXES:
_ : (rvld `ℕ ∷ []) ⊢ ` 0    -- outer 3↓↓ : A = Y (non-closed), over Δ ↓ 0
_ = wf-var here-rvld
_ : [] ⊢ `ℕ                 -- inner 3↓↓ : A = ℕ, over (Δ ↓ 0) ↓ 0 = []
_ = wf-ℕ

------------------------------------------------------------------------
-- Example 2 — a sealed function (notes Example 2)
------------------------------------------------------------------------

-- typing:  (λn:ℕ.n)↓[X:=ℕ]@(X→X) : X→X   at context  X:=ℕ.
-- B = X→X is well-formed (X revealed); the body is checked at (X→X)[X:=ℕ] = ℕ→ℕ
-- and its own λ rebuilds a fresh term context from [].
_ : (rvld `ℕ ∷ []) ∣ [] ⊢ (ƛ `ℕ ∙ ` 0) ↓[ 0 , `ℕ , (` 0 ⇒ ` 0) ] ⦂ (` 0 ⇒ ` 0)
_ = ⊢↓ here (wf-⇒ (wf-var here-rvld) (wf-var here-rvld))
        (⊢ƛ wf-ℕ (⊢` here))

------------------------------------------------------------------------
-- Example 3 — (ΛX. λf:(∀Z.Z→Z). f [X]) [𝔹] · ((ΛY. ΛZ. λz:Z. z) [ℕ])
------------------------------------------------------------------------

private
  zz : Term         -- λz:Z. z
  zz = ƛ ` 0 ∙ ` 0
  fX : Term         -- λf:(∀Z.Z→Z). f [X]
  fX = ƛ (`∀ (` 0 ⇒ ` 0)) ∙ ((` 0) ·[ (` 0 ⇒ ` 0) , ` 0 ])

-- reduction:  -↠ (λz:Z.z) ↑[Z:=𝔹] ↑[Y:=ℕ]   (uses TyWrapCncl, TyWrapRevl, Cancel)
_ : ((Λ fX) ·[ ((`∀ (` 0 ⇒ ` 0)) ⇒ (` 0 ⇒ ` 0)) , `𝔹 ])
      · ((Λ (Λ zz)) ·[ (`∀ (` 0 ⇒ ` 0)) , `ℕ ])
    -↠ (zz ↑[ `𝔹 , (` 0 ⇒ ` 0) ]) ↑[ `ℕ , (`𝔹 ⇒ `𝔹) ]
_ =
    ((Λ fX) ·[ ((`∀ (` 0 ⇒ ` 0)) ⇒ (` 0 ⇒ ` 0)) , `𝔹 ])
      · ((Λ (Λ zz)) ·[ (`∀ (` 0 ⇒ ` 0)) , `ℕ ])
  -→⟨ ξ-·-l (β-Λ (V-G G-ƛ)) ⟩                              -- TyBeta (function)
    (fX ↑[ `𝔹 , ((`∀ (` 0 ⇒ ` 0)) ⇒ (` 0 ⇒ ` 0)) ])
      · ((Λ (Λ zz)) ·[ (`∀ (` 0 ⇒ ` 0)) , `ℕ ])
  -→⟨ ξ-·-r (V-G (G-↑ G-ƛ)) (β-Λ (V-G (G-Λ (V-G G-ƛ)))) ⟩  -- TyBeta (argument)
    (fX ↑[ `𝔹 , ((`∀ (` 0 ⇒ ` 0)) ⇒ (` 0 ⇒ ` 0)) ])
      · ((Λ zz) ↑[ `ℕ , (`∀ (` 0 ⇒ ` 0)) ])
  -→⟨ β-↑ G-ƛ (V-G (G-↑ (G-Λ (V-G G-ƛ)))) ⟩                -- WrapReveal
    (fX · (((Λ zz) ↑[ `ℕ , (`∀ (` 0 ⇒ ` 0)) ]) ↓[ 0 , `𝔹 , (`∀ (` 0 ⇒ ` 0)) ]))
      ↑[ `𝔹 , (` 0 ⇒ ` 0) ]
  -→⟨ ξ-↑ (β-ƛ (V-↓ (V-G (G-↑ (G-Λ (V-G G-ƛ)))))) ⟩        -- Beta
    ((((Λ zz) ↑[ `ℕ , (`∀ (` 0 ⇒ ` 0)) ]) ↓[ 0 , `𝔹 , (`∀ (` 0 ⇒ ` 0)) ])
      ·[ (` 0 ⇒ ` 0) , ` 0 ]) ↑[ `𝔹 , (` 0 ⇒ ` 0) ]
  -→⟨ ξ-↑ (β-↓[] (V-G (G-↑ (G-Λ (V-G G-ƛ))))) ⟩            -- TyWrapCncl
    ((((Λ zz) ↑[ `ℕ , (`∀ (` 0 ⇒ ` 0)) ]) ·[ (` 0 ⇒ ` 0) , `𝔹 ])
      ↓[ 0 , `𝔹 , (` 0 ⇒ ` 0) ]) ↑[ `𝔹 , (` 0 ⇒ ` 0) ]
  -→⟨ ξ-↑ (ξ-↓ (β-↑[] (G-Λ (V-G G-ƛ)))) ⟩                 -- TyWrapRevl
    ((((Λ zz) ·[ (` 0 ⇒ ` 0) , `𝔹 ]) ↑[ `ℕ , (`𝔹 ⇒ `𝔹) ])
      ↓[ 0 , `𝔹 , (` 0 ⇒ ` 0) ]) ↑[ `𝔹 , (` 0 ⇒ ` 0) ]
  -→⟨ ξ-↑ (ξ-↓ (ξ-↑ (β-Λ (V-G G-ƛ)))) ⟩                   -- TyBeta
    (((zz ↑[ `𝔹 , (` 0 ⇒ ` 0) ]) ↑[ `ℕ , (`𝔹 ⇒ `𝔹) ])
      ↓[ 0 , `𝔹 , (` 0 ⇒ ` 0) ]) ↑[ `𝔹 , (` 0 ⇒ ` 0) ]
  -→⟨ β-cancel (V-G (G-↑ (G-↑ G-ƛ))) ⟩                     -- Cancel
    (zz ↑[ `𝔹 , (` 0 ⇒ ` 0) ]) ↑[ `ℕ , (`𝔹 ⇒ `𝔹) ]
  ∎

------------------------------------------------------------------------
-- Example 4 — (ΛX. λx:X. 7) [ℕ] · 5
------------------------------------------------------------------------

-- reduction:  -↠ 7   (TyBeta, WrapReveal, Beta, RevealCnst)
_ : ((Λ (ƛ ` 0 ∙ $ 7)) ·[ (` 0 ⇒ `ℕ) , `ℕ ]) · ($ 5) -↠ $ 7
_ =
    ((Λ (ƛ ` 0 ∙ $ 7)) ·[ (` 0 ⇒ `ℕ) , `ℕ ]) · ($ 5)
  -→⟨ ξ-·-l (β-Λ (V-G G-ƛ)) ⟩                 -- TyBeta
    ((ƛ ` 0 ∙ $ 7) ↑[ `ℕ , (` 0 ⇒ `ℕ) ]) · ($ 5)
  -→⟨ β-↑ G-ƛ V-$ ⟩                            -- WrapReveal
    ((ƛ ` 0 ∙ $ 7) · ($ 5 ↓[ 0 , `ℕ , ` 0 ])) ↑[ `ℕ , `ℕ ]
  -→⟨ ξ-↑ (β-ƛ (V-↓ V-$)) ⟩                    -- Beta
    ($ 7) ↑[ `ℕ , `ℕ ]
  -→⟨ β-$↑ ⟩                                   -- RevealCnst
    $ 7
  ∎

------------------------------------------------------------------------
-- Example 5 — (ΛX. λf:(X→X)→X. f · (λx:X.x)) [ℕ] · (λg:ℕ→ℕ. g·42)
------------------------------------------------------------------------

private
  g42 : Term        -- λg:ℕ→ℕ. g · 42
  g42 = ƛ (`ℕ ⇒ `ℕ) ∙ ((` 0) · ($ 42))
  idX : Term        -- λx:X. x
  idX = ƛ ` 0 ∙ ` 0

-- typing (the WrapConceal reduct, notes line 232):
--   ((λg:ℕ→ℕ. g·42) · (λx:X.x)↑[X:=ℕ]) ↓[X:=ℕ]@X  :  X   at context  X:=ℕ.
-- Concealment over a NON-value body that re-reveals X fresh inside the seal.
_ : (rvld `ℕ ∷ []) ∣ [] ⊢
      (g42 · (idX ↑[ `ℕ , (` 0 ⇒ ` 0) ])) ↓[ 0 , `ℕ , ` 0 ] ⦂ ` 0
_ = ⊢↓ here (wf-var here-rvld)
        (⊢· (⊢ƛ (wf-⇒ wf-ℕ wf-ℕ) (⊢· (⊢` here) ⊢$))
            (⊢↑ (⊢ƛ (wf-var here-rvld) (⊢` here)) wf-ℕ))

-- reduction:  -↠ 42   (uses WrapConceal and Cancel)
_ : ((Λ (ƛ ((` 0 ⇒ ` 0) ⇒ ` 0) ∙ ((` 0) · idX)))
       ·[ (((` 0 ⇒ ` 0) ⇒ ` 0) ⇒ ` 0) , `ℕ ]) · g42
    -↠ $ 42
_ =
    ((Λ (ƛ ((` 0 ⇒ ` 0) ⇒ ` 0) ∙ ((` 0) · idX)))
       ·[ (((` 0 ⇒ ` 0) ⇒ ` 0) ⇒ ` 0) , `ℕ ]) · g42
  -→⟨ ξ-·-l (β-Λ (V-G G-ƛ)) ⟩                         -- TyBeta
    ((ƛ ((` 0 ⇒ ` 0) ⇒ ` 0) ∙ ((` 0) · idX))
       ↑[ `ℕ , (((` 0 ⇒ ` 0) ⇒ ` 0) ⇒ ` 0) ]) · g42
  -→⟨ β-↑ G-ƛ (V-G G-ƛ) ⟩                             -- WrapReveal
    ((ƛ ((` 0 ⇒ ` 0) ⇒ ` 0) ∙ ((` 0) · idX))
       · (g42 ↓[ 0 , `ℕ , ((` 0 ⇒ ` 0) ⇒ ` 0) ])) ↑[ `ℕ , ` 0 ]
  -→⟨ ξ-↑ (β-ƛ (V-↓ (V-G G-ƛ))) ⟩                     -- Beta
    ((g42 ↓[ 0 , `ℕ , ((` 0 ⇒ ` 0) ⇒ ` 0) ]) · idX) ↑[ `ℕ , ` 0 ]
  -→⟨ ξ-↑ (β-↓· (V-G G-ƛ) (V-G G-ƛ)) ⟩               -- WrapConceal
    ((g42 · (idX ↑[ `ℕ , (` 0 ⇒ ` 0) ])) ↓[ 0 , `ℕ , ` 0 ]) ↑[ `ℕ , ` 0 ]
  -→⟨ ξ-↑ (ξ-↓ (β-ƛ (V-G (G-↑ G-ƛ)))) ⟩              -- Beta
    (((idX ↑[ `ℕ , (` 0 ⇒ ` 0) ]) · ($ 42)) ↓[ 0 , `ℕ , ` 0 ]) ↑[ `ℕ , ` 0 ]
  -→⟨ ξ-↑ (ξ-↓ (β-↑ G-ƛ V-$)) ⟩                       -- WrapReveal
    (((idX · ($ 42 ↓[ 0 , `ℕ , ` 0 ])) ↑[ `ℕ , ` 0 ]) ↓[ 0 , `ℕ , ` 0 ]) ↑[ `ℕ , ` 0 ]
  -→⟨ ξ-↑ (ξ-↓ (ξ-↑ (β-ƛ (V-↓ V-$)))) ⟩              -- Beta
    ((($ 42 ↓[ 0 , `ℕ , ` 0 ]) ↑[ `ℕ , ` 0 ]) ↓[ 0 , `ℕ , ` 0 ]) ↑[ `ℕ , ` 0 ]
  -→⟨ ξ-↑ (ξ-↓ (β-cancel V-$)) ⟩                      -- Cancel
    ($ 42 ↓[ 0 , `ℕ , ` 0 ]) ↑[ `ℕ , ` 0 ]
  -→⟨ β-cancel V-$ ⟩                                  -- Cancel
    $ 42
  ∎

------------------------------------------------------------------------
-- Example 6 — (ΛX. λw:ℕ. (ΛY. w) [X→X]) [ℕ] · 5
------------------------------------------------------------------------

private
  -- context  X:=ℕ, Y:=(X→X)   (Y at index 0, rep X→X mentions X; X at index 1)
  Δ₆ : TCtx
  Δ₆ = rvld (` 0 ⇒ ` 0) ∷ rvld `ℕ ∷ []

-- typing:  5↓[X:=ℕ]@ℕ  concealing X at INDEX 1, past a revealed Y whose rep
-- mentions the concealed X.  Stresses the representation lookup (skip-rvld).
_ : Δ₆ ∣ [] ⊢ ($ 5) ↓[ 1 , `ℕ , `ℕ ] ⦂ `ℕ
_ = ⊢↓ (skip-rvld here) wf-ℕ ⊢$

-- variant with annotation B = X, exercising the X-at-0 frame at index 1: the
-- annotation ` 0 is X in the frame rvld ℕ ∷ (Δ₆ ↓ 1) = rvld ℕ ∷ [], and the
-- result type shifts it up to ` 1 (= X in Δ₆) via renameᵗ (1 +_).
_ : Δ₆ ∣ [] ⊢ ($ 5) ↓[ 1 , `ℕ , ` 0 ] ⦂ ` 1
_ = ⊢↓ (skip-rvld here) (wf-var here-rvld) ⊢$

_ : Δ₆ ⊢ `ℕ                                      -- the representation A = ℕ
_ = wf-ℕ

-- reduction:  -↠ 5   (uses Drop, Cancel; and the ⇑ᵀ push of a conceal under Λ)
_ : ((Λ (ƛ `ℕ ∙ ((Λ (` 0)) ·[ `ℕ , (` 0 ⇒ ` 0) ]))) ·[ (`ℕ ⇒ `ℕ) , `ℕ ]) · ($ 5) -↠ $ 5
_ =
    ((Λ (ƛ `ℕ ∙ ((Λ (` 0)) ·[ `ℕ , (` 0 ⇒ ` 0) ]))) ·[ (`ℕ ⇒ `ℕ) , `ℕ ]) · ($ 5)
  -→⟨ ξ-·-l (β-Λ (V-G G-ƛ)) ⟩                       -- TyBeta
    ((ƛ `ℕ ∙ ((Λ (` 0)) ·[ `ℕ , (` 0 ⇒ ` 0) ])) ↑[ `ℕ , (`ℕ ⇒ `ℕ) ]) · ($ 5)
  -→⟨ β-↑ G-ƛ V-$ ⟩                                  -- WrapReveal
    ((ƛ `ℕ ∙ ((Λ (` 0)) ·[ `ℕ , (` 0 ⇒ ` 0) ])) · ($ 5 ↓[ 0 , `ℕ , `ℕ ])) ↑[ `ℕ , `ℕ ]
  -→⟨ ξ-↑ (β-ƛ (V-↓ V-$)) ⟩                          -- Beta (conceal pushed under Λ: ⇑ᵀ)
    ((Λ ($ 5 ↓[ 1 , `ℕ , `ℕ ])) ·[ `ℕ , (` 0 ⇒ ` 0) ]) ↑[ `ℕ , `ℕ ]
  -→⟨ ξ-↑ (β-Λ (V-↓ V-$)) ⟩                          -- TyBeta (into the conceal)
    (($ 5 ↓[ 1 , `ℕ , `ℕ ]) ↑[ (` 0 ⇒ ` 0) , `ℕ ]) ↑[ `ℕ , `ℕ ]
  -→⟨ ξ-↑ (β-drop V-$) ⟩                             -- Drop
    ($ 5 ↓[ 0 , `ℕ , `ℕ ]) ↑[ `ℕ , `ℕ ]
  -→⟨ β-cancel V-$ ⟩                                 -- Cancel
    $ 5
  ∎

------------------------------------------------------------------------
-- The Commute redex is REJECTED by the type system.
--
-- Previously  (λx:X. x) ↓[Y:=ℕ]@(X→X) ↑[X:=ℕ]  type-checked: a value mentioning X,
-- sealed on a *different* Y — the Commute branch.  Under the PREFIX design a
-- conceal body is typed in the prefix Δ ↓ X, which drops X's slot AND everything
-- SHALLOWER (indices ≤ X).  Sealing on the outer Y (index 1) types the body
-- λx:X.x in the prefix (rvld ℕ ∷ rvld ℕ ∷ []) ↓ 1 = [], where X (index 0) is out
-- of scope; its domain annotation ` 0 fails [] ⊢ ` 0.  So the redex no longer
-- type-checks — the pathological shape is ruled out.
--
--   _ : (rvld `ℕ ∷ rvld `ℕ ∷ []) ∣ [] ⊢
--         ((ƛ ` 0 ∙ ` 0) ↓[ 1 , `ℕ , (` 0 ⇒ ` 0) ]) ↑[ `ℕ , (` 0 ⇒ ` 0) ]
--         ⦂ (`ℕ ⇒ `ℕ)                                   -- DOES NOT TYPE
--
-- (The Commute reduction rule has been removed accordingly: no well-typed term
--  takes that branch, so reveal-over-conceal on a different variable is always
--  Drop.)
------------------------------------------------------------------------
