module CoverageFresh where

-- File Charter:
--   * Rule-coverage report for `ReductionFresh`/raw rules as exercised by
--   * the executable terms in `ExamplesFresh`.
--   * Uses `EvalPartialFresh.trace?` to collect per-step `RuleTag`s.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (yes; no)

open import Types
open import Terms
open import EvalPartialFresh
open import ExamplesFresh

rule-code : RuleTag → ℕ
rule-code rule-β = 0
rule-code rule-β-up-∀ = 1
rule-code rule-β-up-↦ = 2
rule-code rule-β-down-↦ = 3
rule-code rule-id-up = 4
rule-code rule-id-down = 5
rule-code rule-seal-unseal = 6
rule-code rule-tag-untag-ok = 7
rule-code rule-tag-untag-bad = 8
rule-code rule-β-up-； = 9
rule-code rule-β-down-； = 10
rule-code rule-δ-⊕ = 11
rule-code rule-blame-·₁ = 12
rule-code rule-blame-·₂ = 13
rule-code rule-blame-·α = 14
rule-code rule-blame-up = 15
rule-code rule-blame-down = 16
rule-code rule-blame-⊕₁ = 17
rule-code rule-blame-⊕₂ = 18
rule-code rule-β-Λ = 19
rule-code rule-β-down-∀ = 20
rule-code rule-β-down-ν = 21
rule-code rule-β-up-ν = 22
rule-code rule-ξ-·₁ = 23
rule-code rule-ξ-·₂ = 24
rule-code rule-ξ-·α = 25
rule-code rule-ξ-up = 26
rule-code rule-ξ-down = 27
rule-code rule-ξ-⊕₁ = 28
rule-code rule-ξ-⊕₂ = 29

contains : RuleTag → List RuleTag → Bool
contains r [] = false
contains r (x ∷ xs) with rule-code r ≟ rule-code x
... | yes _ = true
... | no _ = contains r xs

trace-steps-from-empty : Term → List RuleTag
trace-steps-from-empty M = trace-steps gas [] M

all-rule-hits : List RuleTag
all-rule-hits =
  trace-steps-from-empty example1-left ++
  trace-steps-from-empty example1-right ++
  trace-steps-from-empty example2-left ++
  trace-steps-from-empty example2-right ++
  trace-steps-from-empty example3-left ++
  trace-steps-from-empty example3-right ++
  trace-steps-from-empty example4-left ++
  trace-steps-from-empty example4-right ++
  trace-steps-from-empty example5-left ++
  trace-steps-from-empty example5-right ++
  trace-steps-from-empty example6-left ++
  trace-steps-from-empty example6-right ++
  trace-steps-from-empty example7-left ++
  trace-steps-from-empty example7-right ++
  trace-steps-from-empty example8-left ++
  trace-steps-from-empty example8-right ++
  trace-steps-from-empty example9-left ++
  trace-steps-from-empty example9-right ++
  trace-steps-from-empty example10-left ++
  trace-steps-from-empty example10-right ++
  trace-steps-from-empty example12 ++
  trace-steps-from-empty sec2-app-dyn ++
  trace-steps-from-empty sec2-app-base ++
  trace-steps-from-empty sec5-β ++
  trace-steps-from-empty sec6-K-dyn ++
  trace-steps-from-empty sec6-K-base ++
  trace-steps-from-empty sec6-K-lax ++
  trace-steps-from-empty sec6-K-strict ++
  trace-steps-from-empty sec6-id-leak ++
  trace-steps-from-empty seal-name-example ++
  trace-steps-from-empty target-β-up-∀ ++
  trace-steps-from-empty target-tag-untag-bad ++
  trace-steps-from-empty target-β-up-； ++
  trace-steps-from-empty target-β-down-； ++
  trace-steps-from-empty target-δ-⊕ ++
  trace-steps-from-empty target-blame-·₁ ++
  trace-steps-from-empty target-blame-·₂ ++
  trace-steps-from-empty target-blame-·α ++
  trace-steps-from-empty target-blame-down ++
  trace-steps-from-empty target-blame-⊕₁ ++
  trace-steps-from-empty target-blame-⊕₂ ++
  trace-steps-from-empty target-β-Λ ++
  trace-steps-from-empty target-β-down-∀ ++
  trace-steps-from-empty target-β-down-ν ++
  trace-steps-from-empty target-β-up-ν ++
  trace-steps-from-empty target-ξ-·₂ ++
  trace-steps-from-empty target-ξ-·α ++
  trace-steps-from-empty target-ξ-⊕₁ ++
  trace-steps-from-empty target-ξ-⊕₂ ++
  trace-steps-from-empty three-seals-second-β-down-ν

covered : RuleTag → Bool
covered r = contains r all-rule-hits

covers-β-down-ν : Bool
covers-β-down-ν = covered rule-β-down-ν

covers-β-up-ν : Bool
covers-β-up-ν = covered rule-β-up-ν

covers-δ-⊕ : Bool
covers-δ-⊕ = covered rule-δ-⊕

covers-β-up-； : Bool
covers-β-up-； = covered rule-β-up-；

covers-β-down-； : Bool
covers-β-down-； = covered rule-β-down-；
