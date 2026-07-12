module proof.EndpointCanonicalMLBSimpleFactorCounterexample where

-- File Charter:
--   * Records the counterexample to raw cross-context factorization without a
--     target common-lower or selector-success premise.
--   * Justifies the paired-route premise used by the quotient-coherence plan.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Nullary using (¬_)

open import Types
open import Imprecision using (_ˣ⊑ˣ_)
open import ImprecisionWf
open import proof.EndpointCanonicalMLBSimple using (rawEndpointMlbsAt)

factor-context : ImpCtx
factor-context =
  (zero ˣ⊑ˣ zero) ∷ (zero ˣ⊑ˣ suc zero) ∷ []

source-below-left :
  factor-context ∣ 1 ⊢ ＇ zero ⊑ ＇ zero ⊣ 2
source-below-left = idˣ (here refl) z<s z<s

source-below-right :
  factor-context ∣ 1 ⊢ ＇ zero ⊑ ＇ suc zero ⊣ 2
source-below-right = idˣ (there (here refl)) z<s (s<s z<s)

target-raw-empty :
  rawEndpointMlbsAt 2 (＇ zero) (＇ suc zero) ≡ []
target-raw-empty = refl

no-unconditional-raw-factor :
  ¬ (∃[ D ]
      (D ∈ rawEndpointMlbsAt 2 (＇ zero) (＇ suc zero) ×
       factor-context ∣ 1 ⊢ ＇ zero ⊑ D ⊣ 2))
no-unconditional-raw-factor (D , (() , source⊑D))
