module strong.notes.old.Scratch7 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import strong.Types
open import strong.Context
open import strong.notes.old.Terms
open import strong.notes.old.Typing
open import strong.notes.old.Reduction

-- context  index 0 : Y:=ℕ | index 1 : X:=ℕ | index 2 : W:=ℕ   (all reps closed)
Δ7 : TCtx
Δ7 = rvld `ℕ ∷ rvld `ℕ ∷ rvld `ℕ ∷ []

-- F = ΛZ. λz:Z. z   (polymorphic identity), a value in the prefix Δ ↓ 1
F : Term
F = Λ (ƛ ` 0 ∙ ` 0)

------------------------------------------------------------------------
-- POSITIVE case: type argument C = W (` 2), DEEPER than the concealed X.
------------------------------------------------------------------------

-- the redex  (F ↓[X=1, ℕ, ∀(Z→Z)]) [Z→Z, W]  is well typed at  W→W (` 2 ⇒ ` 2)
redex+ : Term
redex+ = (F ↓[ 1 , `ℕ , `∀ (` 0 ⇒ ` 0) ]) ·[ (` 0 ⇒ ` 0) , ` 2 ]

⊢redex+ : Δ7 ∣ [] ⊢ redex+ ⦂ (` 2 ⇒ ` 2)
⊢redex+ = ⊢·[] (⊢↓ (skip-rvld here)
                   (wf-∀ (wf-⇒ (wf-var here-abst) (wf-var here-abst)))
                   (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))))
               (wf-var (skip-rvld (skip-rvld here-rvld)))

-- one β-↓[] step
step+ : redex+ -→ (F ·[ ` 0 ⇒ ` 0 , ` 0 ]) ↓[ 1 , `ℕ , (` 1 ⇒ ` 1) ]
step+ = β-↓[] (V-G (G-Λ (V-G G-ƛ)))

-- PRESERVATION: the reduct is well typed at the SAME type  W→W
⊢reduct+ : Δ7 ∣ [] ⊢ (F ·[ ` 0 ⇒ ` 0 , ` 0 ]) ↓[ 1 , `ℕ , (` 1 ⇒ ` 1) ] ⦂ (` 2 ⇒ ` 2)
⊢reduct+ = ⊢↓ (skip-rvld here)
              (wf-⇒ (wf-var (skip-rvld here-rvld)) (wf-var (skip-rvld here-rvld)))
              (⊢·[] (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))) (wf-var here-rvld))

------------------------------------------------------------------------
-- NEGATIVE case: type argument C = Y (` 0), SHALLOWER than the concealed X.
------------------------------------------------------------------------

-- the redex  (F ↓[X=1, ℕ, ∀(Z→Z)]) [Z→Z, Y]  is well typed at  Y→Y (` 0 ⇒ ` 0)
redex- : Term
redex- = (F ↓[ 1 , `ℕ , `∀ (` 0 ⇒ ` 0) ]) ·[ (` 0 ⇒ ` 0) , ` 0 ]

⊢redex- : Δ7 ∣ [] ⊢ redex- ⦂ (` 0 ⇒ ` 0)
⊢redex- = ⊢·[] (⊢↓ (skip-rvld here)
                   (wf-∀ (wf-⇒ (wf-var here-abst) (wf-var here-abst)))
                   (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here))))
               (wf-var here-rvld)

-- one β-↓[] step: the argument Y (` 0) is reindexed by downTyEnv 1 ℕ, which sends
-- 0 ↦ ` (0 ∸ 2) = ` 0 — but ` 0 in the prefix is W, NOT Y!  And the re-conceal's
-- annotation becomes ` 0 ⇒ ` 0, so its type is renameᵗ (1 +_) (` 0 ⇒ ` 0) = ` 1 ⇒ ` 1.
step- : redex- -→ (F ·[ ` 0 ⇒ ` 0 , ` 0 ]) ↓[ 1 , `ℕ , (` 0 ⇒ ` 0) ]
step- = β-↓[] (V-G (G-Λ (V-G G-ƛ)))

-- The reduct  (F [Z→Z, W]) ↓[1, ℕ, Z→Z]  is ILL-TYPED at every type:
-- the conceal ↓[1,ℕ,`0⇒`0] demands a body of type (`0⇒`0)[ℕ]ᵗ = ℕ→ℕ, but the
-- body F[Z→Z, ` 0] has type (`0⇒`0)[` 0]ᵗ = W→W (the arg ` 0 is W in the prefix).
-- So NO type ascription works — preservation FAILS for β-↓[] here.  Ascribing the
-- reduct either the preserved type (` 0 ⇒ ` 0) or (` 1 ⇒ ` 1) both fail to type
-- check with the same body error:  (`0⇒`0)[` 0]ᵗ != (`0⇒`0)[`ℕ]ᵗ.
