module strong.notes.old.Scratch9 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import strong.Types
open import strong.Context
open import strong.notes.old.Terms
open import strong.notes.old.Typing
open import strong.notes.old.Reduction
open import strong.notes.old.Scratch8 using (polyid; P; ⊢P)

-- T4 : the ill-typed term produced by TyWrapCncl (end of Scratch8)
T4 : Term
T4 = (Λ ((polyid ·[ (` 0 ⇒ ` 0) , ` 0 ]) ↓[ 1 , `ℕ , (` 0 ⇒ ` 0) ])) ↑[ `ℕ , `∀ (` 0 ⇒ ` 0) ]

-- T5 : one more step — TyBeta fires on the inner (polyid [Y]) = (ΛZ.λz.z) [Y]
T5 : Term
T5 = (Λ (((ƛ ` 0 ∙ ` 0) ↑[ ` 0 , (` 0 ⇒ ` 0) ]) ↓[ 1 , `ℕ , (` 0 ⇒ ` 0) ])) ↑[ `ℕ , `∀ (` 0 ⇒ ` 0) ]

-- the extra step  T4 -→ T5  (TyBeta under ↑, Λ, ↓)
step45 : T4 -→ T5
step45 = ξ-↑ (ξ-Λ (ξ-↓ (β-Λ (V-G G-ƛ))))

-- T5 is a VALUE — the normal form; no further reduction fires
T5-value : Value T5
T5-value = V-G (G-↑ (G-Λ (V-↓ (V-G (G-↑ G-ƛ)))))
