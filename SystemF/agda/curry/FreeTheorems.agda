{-# OPTIONS --cumulativity --omega-in-omega #-}
module curry.FreeTheorems where

-- File Charter:
--   * Public free-theorem interface for curry System F.
--   * Exposes identity and representation-independence theorems.
--   * Delegates proof scripts to `curry.proof.FreeTheorems`.

open import curry.ProductOmega using (∃-syntax; _×_)
open import curry.Reduction
open import Data.List using ([])

import curry.proof.FreeTheorems as FreeTheoremsProof

open FreeTheoremsProof public using (neg; flip; R)

free-theorem-id : ∀ {A : Ty}
  → (M V : Term)
  → 0 ⊢ [] ⊢ M ⦂ `∀ (` 0 ⇒ ` 0)
  → 0 ⊢ [] ⊢ V ⦂ A
  → Value V
  → ((M ·[]) · V) —↠ V
free-theorem-id = FreeTheoremsProof.free-theorem-id

free-theorem-rep :
  ∀ (M : Term)
  → 0 ⊢ [] ⊢ M ⦂ `∀ (` 0 ⇒ (` 0 ⇒ ` 0) ⇒ ` 0)
  → ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
      (((M ·[]) · `true)        · neg  —↠ V)
    × (((M ·[]) · (`suc `zero)) · flip —↠ W)
    × R V W v w
free-theorem-rep = FreeTheoremsProof.free-theorem-rep
