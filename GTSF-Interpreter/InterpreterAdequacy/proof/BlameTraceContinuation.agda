module InterpreterAdequacy.proof.BlameTraceContinuation where

-- File Charter:
--   * Propagates exact blame traces through evaluation frames.
--   * Joins successful return prefixes to later blame computations while
--     accounting for allocation-induced renaming of earlier values.
--   * Contains no interpreter recursion or evaluator case analysis.

open import Data.List using ([]; _∷_; _++_)

open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.BlameTrace
open import InterpreterAdequacy.proof.ReturnTrace
open import InterpreterAdequacy.proof.TraceAgreementPath using
  (value-trace-path-empty; value-trace-rebase)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  ( value-trace-no-bullet
  ; value-trace-value
  ; world-trace-agreement-++
  ; world-trace-path-++
  )
open import NuReduction using
  ( applyTerms
  ; keep
  ; blame-·₁
  ; blame-·₂
  ; blame-⟨⟩
  ; blame-⊕₁
  ; blame-⊕₂
  ; blame-ν
  ; pure-step
  ; _—→_
  ; _—↠[_]_
  ; ↠-refl
  ; ↠-step
  )
import NuTerms as N
open import proof.Core.Properties.ReductionProperties using
  ( applyCoercions
  ; cast-↠
  ; ν-↠
  ; ⊕₁-↠
  ; ⊕₂-↠
  ; ·₁-↠
  ; ·₂-↠
  ; ↠-trans
  )

prepend-pure-step-to-blame :
  ∀ {W U prefix P Q}
    {world-agreement : WorldTraceAgreement W prefix} →
  P —→ Q →
  BlameTrace world-agreement Q U →
  BlameTrace world-agreement P U
prepend-pure-step-to-blame step
    (blame-trace changes path reduction) =
  blame-trace (keep ∷ changes) (world-trace-keep path)
    (↠-step (pure-step step) reduction)

propagate-cast-blame :
  ∀ {W U prefix P c}
    {world-agreement : WorldTraceAgreement W prefix} →
  BlameTrace world-agreement P U →
  BlameTrace world-agreement (P N.⟨ c ⟩) U
propagate-cast-blame {c = c}
    (blame-trace χP path-P P-reduction) =
  blame-trace (χP ++ keep ∷ [])
    (world-trace-path-++ path-P (world-trace-keep world-trace-done))
    (↠-trans (cast-↠ P-reduction)
      (↠-step (pure-step blame-⟨⟩) ↠-refl))

propagate-application-left-blame :
  ∀ {W U prefix L M}
    {world-agreement : WorldTraceAgreement W prefix} →
  N.No• M →
  BlameTrace world-agreement L U →
  BlameTrace world-agreement (L N.· M) U
propagate-application-left-blame no-M
    (blame-trace χL path-L L-reduction) =
  blame-trace (χL ++ keep ∷ [])
    (world-trace-path-++ path-L (world-trace-keep world-trace-done))
    (↠-trans (·₁-↠ no-M L-reduction)
      (↠-step (pure-step blame-·₁) ↠-refl))

propagate-primitive-left-blame :
  ∀ {W U prefix L M op}
    {world-agreement : WorldTraceAgreement W prefix} →
  N.No• M →
  BlameTrace world-agreement L U →
  BlameTrace world-agreement (L N.⊕[ op ] M) U
propagate-primitive-left-blame no-M
    (blame-trace χL path-L L-reduction) =
  blame-trace (χL ++ keep ∷ [])
    (world-trace-path-++ path-L (world-trace-keep world-trace-done))
    (↠-trans (⊕₁-↠ no-M L-reduction)
      (↠-step (pure-step blame-⊕₁) ↠-refl))

propagate-nu-left-blame :
  ∀ {W U prefix A L c}
    {world-agreement : WorldTraceAgreement W prefix} →
  BlameTrace world-agreement L U →
  BlameTrace world-agreement (N.ν A L c) U
propagate-nu-left-blame
    (blame-trace χL path-L L-reduction) =
  blame-trace (χL ++ keep ∷ [])
    (world-trace-path-++ path-L (world-trace-keep world-trace-done))
    (↠-trans (ν-↠ L-reduction)
      (↠-step blame-ν ↠-refl))

propagate-application-right-blame :
  ∀ {W U prefix F f P}
    {world-agreement : WorldTraceAgreement W prefix} →
  ValueTraceAgreement world-agreement [] F f →
  BlameTrace world-agreement P U →
  BlameTrace world-agreement (f N.· P) U
propagate-application-right-blame F-agrees
    (blame-trace χP path-P P-reduction) =
  blame-trace (χP ++ keep ∷ [])
    (world-trace-path-++ path-P (world-trace-keep world-trace-done))
    (↠-trans
      (·₂-↠ (value-trace-value F-agrees)
        (value-trace-no-bullet F-agrees) P-reduction)
      (↠-step
        (pure-step (blame-·₂ (value-trace-value F-after-path))) ↠-refl))
  where
  F-after-path = value-trace-path-empty _ path-P F-agrees

propagate-primitive-right-blame :
  ∀ {W U prefix F f P op}
    {world-agreement : WorldTraceAgreement W prefix} →
  ValueTraceAgreement world-agreement [] F f →
  BlameTrace world-agreement P U →
  BlameTrace world-agreement (f N.⊕[ op ] P) U
propagate-primitive-right-blame F-agrees
    (blame-trace χP path-P P-reduction) =
  blame-trace (χP ++ keep ∷ [])
    (world-trace-path-++ path-P (world-trace-keep world-trace-done))
    (↠-trans
      (⊕₂-↠ (value-trace-value F-agrees)
        (value-trace-no-bullet F-agrees) P-reduction)
      (↠-step
        (pure-step (blame-⊕₂ (value-trace-value F-after-path))) ↠-refl))
  where
  F-after-path = value-trace-path-empty _ path-P F-agrees

continue-under-cast-to-blame :
  ∀ {W U Z prefix χP P v c}
    (world-agreement : WorldTraceAgreement W prefix)
    (path-P : WorldTracePath W χP U) →
  P —↠[ χP ] v →
  BlameTrace
    (world-trace-agreement-++ world-agreement path-P)
    (v N.⟨ applyCoercions χP c ⟩) Z →
  BlameTrace world-agreement (P N.⟨ c ⟩) Z
continue-under-cast-to-blame world-agreement path-P P-reduction
    (blame-trace χC path-C C-reduction) =
  blame-trace (_ ++ χC)
    (world-trace-path-++ path-P path-C)
    (↠-trans (cast-↠ P-reduction) C-reduction)

continue-application-after-argument-return-to-blame :
  ∀ {W U Z prefix χP F f P u}
    (world-agreement : WorldTraceAgreement W prefix)
    (path-P : WorldTracePath W χP U) →
  ValueTraceAgreement world-agreement [] F f →
  P —↠[ χP ] u →
  BlameTrace
    (world-trace-agreement-++ world-agreement path-P)
    (applyTerms χP f N.· u) Z →
  BlameTrace world-agreement (f N.· P) Z
continue-application-after-argument-return-to-blame
    world-agreement path-P F-agrees P-reduction
    (blame-trace χA path-A A-reduction) =
  blame-trace (_ ++ χA)
    (world-trace-path-++ path-P path-A)
    (↠-trans
      (·₂-↠ (value-trace-value F-agrees)
        (value-trace-no-bullet F-agrees) P-reduction)
      A-reduction)

continue-application-after-argument-return :
  ∀ {W U Z prefix χP F f P u R}
    (world-agreement : WorldTraceAgreement W prefix)
    (path-P : WorldTracePath W χP U) →
  ValueTraceAgreement world-agreement [] F f →
  P —↠[ χP ] u →
  ReturnTrace
    (world-trace-agreement-++ world-agreement path-P)
    (applyTerms χP f N.· u) Z R →
  ReturnTrace world-agreement (f N.· P) Z R
continue-application-after-argument-return
    world-agreement path-P F-agrees P-reduction
    (return-trace χA z path-A A-reduction R-agrees) =
  return-trace (_ ++ χA) z
    (world-trace-path-++ path-P path-A)
    (↠-trans
      (·₂-↠ (value-trace-value F-agrees)
        (value-trace-no-bullet F-agrees) P-reduction)
      A-reduction)
    (value-trace-rebase R-agrees)

continue-application-after-function-return-to-blame :
  ∀ {W U Z prefix χL L f M}
    (world-agreement : WorldTraceAgreement W prefix)
    (path-L : WorldTracePath W χL U) →
  N.No• M →
  L —↠[ χL ] f →
  BlameTrace
    (world-trace-agreement-++ world-agreement path-L)
    (f N.· applyTerms χL M) Z →
  BlameTrace world-agreement (L N.· M) Z
continue-application-after-function-return-to-blame
    world-agreement path-L no-M L-reduction
    (blame-trace χA path-A A-reduction) =
  blame-trace (_ ++ χA)
    (world-trace-path-++ path-L path-A)
    (↠-trans (·₁-↠ no-M L-reduction) A-reduction)

continue-primitive-after-left-return-to-blame :
  ∀ {W U Z prefix χL L f M op}
    (world-agreement : WorldTraceAgreement W prefix)
    (path-L : WorldTracePath W χL U) →
  N.No• M →
  L —↠[ χL ] f →
  BlameTrace
    (world-trace-agreement-++ world-agreement path-L)
    (f N.⊕[ op ] applyTerms χL M) Z →
  BlameTrace world-agreement (L N.⊕[ op ] M) Z
continue-primitive-after-left-return-to-blame
    world-agreement path-L no-M L-reduction
    (blame-trace χA path-A A-reduction) =
  blame-trace (_ ++ χA)
    (world-trace-path-++ path-L path-A)
    (↠-trans (⊕₁-↠ no-M L-reduction) A-reduction)
