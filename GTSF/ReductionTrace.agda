module ReductionTrace where

-- File Charter:
--   * Gives readable names to Nu reduction rules while preserving evaluation
--     context nesting.
--   * Converts checked multi-step and evaluator traces to lists suitable for
--     executable regression examples.
--   * Depends only on the Nu reduction semantics and raw evaluator.

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

import Eval as Eval
open import NuReduction

data PureStepName : Set where
  δ-⊕-step β-ƛ-step β-Λ•-step : PureStepName
  β-∀•-step β-gen•-step : PureStepName
  β-id-step β-seq-step β-↦-step β-inst-step : PureStepName
  tag-untag-ok-step tag-untag-bad-step seal-unseal-step : PureStepName
  blame-·₁-step blame-·₂-step blame-•-step : PureStepName
  blame-cast-step : PureStepName
  blame-⊕₁-step blame-⊕₂-step : PureStepName

pure-step-name : ∀ {M N} → M —→ N → PureStepName
pure-step-name δ-⊕ = δ-⊕-step
pure-step-name (β vV) = β-ƛ-step
pure-step-name (β-Λ• vV) = β-Λ•-step
pure-step-name (β-∀• vV) = β-∀•-step
pure-step-name (β-gen• vV) = β-gen•-step
pure-step-name (β-id vV) = β-id-step
pure-step-name (β-seq vV) = β-seq-step
pure-step-name (β-↦ vV vW) = β-↦-step
pure-step-name (β-inst vV) = β-inst-step
pure-step-name (tag-untag-ok vV) = tag-untag-ok-step
pure-step-name (tag-untag-bad vV neq) = tag-untag-bad-step
pure-step-name (seal-unseal vV) = seal-unseal-step
pure-step-name blame-·₁ = blame-·₁-step
pure-step-name (blame-·₂ vV) = blame-·₂-step
pure-step-name blame-• = blame-•-step
pure-step-name blame-⟨⟩ = blame-cast-step
pure-step-name blame-⊕₁ = blame-⊕₁-step
pure-step-name (blame-⊕₂ vV) = blame-⊕₂-step

data StepName : Set where
  root : PureStepName → StepName
  allocate-ν : StepName
  under-app-left under-app-right under-cast under-ν :
    StepName → StepName
  blame-ν-step : StepName
  under-⊕-left under-⊕-right : StepName → StepName

step-name : ∀ {M χ N} → M —→[ χ ] N → StepName
step-name (pure-step M→N) = root (pure-step-name M→N)
step-name (ν-step vV noV) = allocate-ν
step-name (ξ-·₁ L→L′ shiftM) = under-app-left (step-name L→L′)
step-name (ξ-·₂ vV shiftV M→M′) = under-app-right (step-name M→M′)
step-name (ξ-⟨⟩ M→M′) = under-cast (step-name M→M′)
step-name (ξ-ν L→L′) = under-ν (step-name L→L′)
step-name blame-ν = blame-ν-step
step-name (ξ-⊕₁ L→L′ shiftM) = under-⊕-left (step-name L→L′)
step-name (ξ-⊕₂ vL shiftL M→M′) =
  under-⊕-right (step-name M→M′)

trace-step-names : ∀ {M χs N} → M —↠[ χs ] N → List StepName
trace-step-names ↠-refl = []
trace-step-names (↠-step M→N N↠P) =
  step-name M→N ∷ trace-step-names N↠P

outcome-step-names :
  ∀ {M} →
  Maybe (Eval.EvalOutcome M) →
  Maybe (List StepName)
outcome-step-names nothing = nothing
outcome-step-names (just r) =
  just (trace-step-names (Eval.outcomeTrace r))
