module proof.MilestoneOneExamples where

-- File Charter:
--   * Private proofs for the public Milestone 1 examples.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat renaming (zero to zeroℕ; suc to sucℕ)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)

open import STLCRef
open import GroundInterface
open import GroundBisimulation

private-garbage : Term
private-garbage = (ƛ ref nat ⇒ `unit) · ref `zero

private-garbage-↠ :
  (private-garbage , []) —↠ (`unit , `zero ∷ [])
private-garbage-↠ =
    private-garbage , []
  —→⟨ ξ-·₂ (ƛ ref nat ⇒ `unit) (β-ref `zero) ⟩
    (ƛ ref nat ⇒ `unit) · `loc zeroℕ , `zero ∷ []
  —→⟨ β-ƛ (`loc zeroℕ) ⟩
    `unit , `zero ∷ []
  ∎

zero≢one : zeroℕ ≡ sucℕ zeroℕ -> ⊥
zero≢one ()

zero≉one :
  exposed (nat-result zeroℕ) [] ≈
  exposed (nat-result (sucℕ zeroℕ)) [] -> ⊥
zero≉one bisim = zero≢one (nat-observation-injective bisim)
