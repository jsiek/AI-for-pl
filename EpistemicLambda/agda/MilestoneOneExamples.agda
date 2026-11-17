module MilestoneOneExamples where

-- File Charter:
--   * Public Milestone 1 examples and theorem statements.
--   * Connects the STLCRef reduction semantics to observer states.
--   * Exercises private garbage, fresh-address abstraction, public references,
--     distinct naturals, and termination versus divergence.

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat renaming (zero to zeroℕ; suc to sucℕ)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)

open import STLCRef
open import GroundInterface
open import GroundBisimulation

import proof.MilestoneOneExamples as ExampleProof

private-garbage : Term
private-garbage = (ƛ ref nat ⇒ `unit) · ref `zero

private-garbage-⊢ : [] ∣ [] ⊢ private-garbage ⦂ unit
private-garbage-⊢ = ⊢· (⊢ƛ ⊢unit) (⊢ref ⊢zero)

private-garbage-↠ :
  (private-garbage , []) —↠ (`unit , `zero ∷ [])
private-garbage-↠ = ExampleProof.private-garbage-↠

private-garbage-execution : private-garbage ⇓[ unit-result ] (`zero ∷ [])
private-garbage-execution =
  returns-unit private-garbage-⊢ private-garbage-↠

unit-execution : `unit ⇓[ unit-result ] []
unit-execution = returns-unit ⊢unit ((`unit , []) ∎)

private-garbage≈unit :
  initial-state private-garbage-execution ≈ initial-state unit-execution
private-garbage≈unit = unit-heaps-bisimilar

fresh-addresses≈ :
  exposed (ref-result zeroℕ) (`zero ∷ []) ≈
  exposed (ref-result (sucℕ zeroℕ)) (`zero ∷ `zero ∷ [])
fresh-addresses≈ =
  renamed-reference-bisimilar (relate-key refl (zeroℕ , refl))

public-addresses≈ :
  public-ref zeroℕ (`zero ∷ []) ≈
  public-ref (sucℕ zeroℕ) (`zero ∷ `zero ∷ [])
public-addresses≈ =
  public-reference-bisimilar (relate-key refl (zeroℕ , refl))

zero≉one :
  exposed (nat-result zeroℕ) [] ≈
  exposed (nat-result (sucℕ zeroℕ)) [] -> ⊥
zero≉one = ExampleProof.zero≉one

unit≉diverging : exposed unit-result [] ≈ diverging -> ⊥
unit≉diverging = unit-not-bisimilar-diverging
