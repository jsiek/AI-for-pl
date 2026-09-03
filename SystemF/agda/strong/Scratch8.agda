module strong.Scratch8 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import strong.Types
open import strong.Context
open import strong.Terms
open import strong.Typing
open import strong.Reduction

-- ΛZ. λz:Z. z   (polymorphic identity), a closed value of type ∀Z. Z→Z
polyid : Term
polyid = Λ (ƛ ` 0 ∙ ` 0)

-- λf:(∀Z.Z→Z). ΛY. f [Y]      (f applied to a FRESH type variable Y)
fn : Term
fn = ƛ (`∀ (` 0 ⇒ ` 0)) ∙ (Λ ((` 0) ·[ (` 0 ⇒ ` 0) , ` 0 ]))

-- CLOSED program:  (ΛX. λf:(∀Z.Z→Z). ΛY. f [Y]) [ℕ] · (ΛZ. λz:Z. z)
P : Term
P = ((Λ fn) ·[ ((`∀ (` 0 ⇒ ` 0)) ⇒ (`∀ (` 0 ⇒ ` 0))) , `ℕ ]) · polyid

-- P is well typed (closed) at  ∀Y. Y→Y
⊢P : [] ∣ [] ⊢ P ⦂ `∀ (` 0 ⇒ ` 0)
⊢P = ⊢· (⊢·[] (⊢Λ (⊢ƛ (wf-∀ (wf-⇒ (wf-var here-abst) (wf-var here-abst)))
                       (⊢Λ (⊢·[] (⊢` here)
                                 (wf-var here-abst)))))
              wf-ℕ)
        (⊢Λ (⊢ƛ (wf-var here-abst) (⊢` here)))

------------------------------------------------------------------------
-- P reduces in 4 steps to a term whose 4th step is the counterexample.
------------------------------------------------------------------------

-- After 3 steps the argument polyid has been concealed on X and BUMPED to index 1
-- (pushed under ΛY); the redex  (polyid ↓[1,ℕ,∀(Z→Z)]) [Z→Z, Y]  type-applies a
-- conceal at X (index 1) to the SHALLOWER Y (index 0).  The 4th step is β-↓[].
_ : P -↠ (Λ ((polyid ·[ (` 0 ⇒ ` 0) , ` 0 ]) ↓[ 1 , `ℕ , (` 0 ⇒ ` 0) ])) ↑[ `ℕ , `∀ (` 0 ⇒ ` 0) ]
_ =
    P
  -→⟨ ξ-·-l (β-Λ (V-G G-ƛ)) ⟩                                   -- TyBeta
    (fn ↑[ `ℕ , ((`∀ (` 0 ⇒ ` 0)) ⇒ (`∀ (` 0 ⇒ ` 0))) ]) · polyid
  -→⟨ β-↑ G-ƛ (V-G (G-Λ (V-G G-ƛ))) ⟩                           -- WrapReveal
    (fn · (polyid ↓[ 0 , `ℕ , (`∀ (` 0 ⇒ ` 0)) ])) ↑[ `ℕ , (`∀ (` 0 ⇒ ` 0)) ]
  -→⟨ ξ-↑ (β-ƛ (V-↓ (V-G (G-Λ (V-G G-ƛ))))) ⟩                   -- Beta (conceal bumped to index 1)
    (Λ ((polyid ↓[ 1 , `ℕ , (`∀ (` 0 ⇒ ` 0)) ]) ·[ (` 0 ⇒ ` 0) , ` 0 ]))
      ↑[ `ℕ , (`∀ (` 0 ⇒ ` 0)) ]
  -→⟨ ξ-↑ (ξ-Λ (β-↓[] (V-G (G-Λ (V-G G-ƛ))))) ⟩                 -- TyWrapCncl  (the counterexample)
    (Λ ((polyid ·[ (` 0 ⇒ ` 0) , ` 0 ]) ↓[ 1 , `ℕ , (` 0 ⇒ ` 0) ]))
      ↑[ `ℕ , (`∀ (` 0 ⇒ ` 0)) ]
  ∎

------------------------------------------------------------------------
-- The final term is ILL-TYPED: inside it, the conceal ↓[1,ℕ,`0⇒`0] has body
--   polyid ·[ `0⇒`0 , ` 0 ]  typed in the prefix (abst ∷ rvld ℕ ∷ []) ↓ 1 = [],
-- but the type argument ` 0 (the shifted Y) is out of scope in the empty prefix:
-- the ⊢·[] for the body needs  [] ⊢ ` 0,  which is false.  So a WELL-TYPED closed
-- program reduces in 4 steps to an ILL-TYPED term — preservation fails outright.
------------------------------------------------------------------------
