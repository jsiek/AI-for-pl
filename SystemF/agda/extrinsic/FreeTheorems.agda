{-# OPTIONS --cumulativity --omega-in-omega #-}
module extrinsic.FreeTheorems where

-- File Charter:
--   * Public free-theorem surface for extrinsic System F.
--   * Exposes identity and representation-independence theorems.

open import Data.List using ([])
open import extrinsic.ProductOmega using (∃-syntax; _×_)

open import extrinsic.Reduction
open import extrinsic.proof.FreeTheorems public hiding (free-theorem-id; free-theorem-rep)
import extrinsic.proof.FreeTheorems as FreeTheoremsProof

free-theorem-id : ∀ {A : Ty}
  → (M V : Term)
  → 0 ∣ [] ⊢ M ⦂ `∀ (` 0 ⇒ ` 0)
  → 0 ∣ [] ⊢ V ⦂ A
  → Value V
  → ((M ·[ A ]) · V) —↠ V
free-theorem-id = FreeTheoremsProof.free-theorem-id

free-theorem-rep :
  ∀ (M : Term)
  → 0 ∣ [] ⊢ M ⦂ `∀ (` 0 ⇒ (` 0 ⇒ ` 0) ⇒ ` 0)
  → ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
      (((M ·[ `Bool ]) · `true) · neg —↠ V)
      × (((M ·[ `ℕ ]) · (`suc `zero)) · flip —↠ W)
      × (∃[ ⊢V ] ∃[ ⊢W ] R V W v w ⊢V ⊢W)
free-theorem-rep = FreeTheoremsProof.free-theorem-rep
