module InterpreterAdequacy.proof.BlameTrace where

-- File Charter:
--   * Packages the result of a successful interpreter-to-small-step blame
--     simulation, retaining the exact world-allocation trace.
--   * Provides transport at the source term and blamed interpreter world.
--   * Contains no interpreter recursion or evaluation case analysis.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Interpreter using (Outcome; World; blamed)
open import InterpreterAdequacy.TraceAgreement
open import NuReduction using (StoreChanges; _—↠[_]_; ↠-refl)
import NuTerms as N

record BlameTrace
    {W χs}
    (world-agreement : WorldTraceAgreement W χs)
    (P : N.Term)
    (U : World) : Set₁ where
  constructor blame-trace
  field
    changes : StoreChanges
    world-path : WorldTracePath W changes U
    reduction-trace : P —↠[ changes ] N.blame

open BlameTrace public

blame-trace-start-eq :
  ∀ {W U χs}
    {world-agreement : WorldTraceAgreement W χs}
    {P Q} →
  P ≡ Q →
  BlameTrace world-agreement Q U →
  BlameTrace world-agreement P U
blame-trace-start-eq term-eq (blame-trace changes path reduction) =
  blame-trace changes path
    (subst (λ P′ → P′ —↠[ changes ] N.blame) (sym term-eq) reduction)

blame-trace-result-eq :
  ∀ {W U Z χs}
    {world-agreement : WorldTraceAgreement W χs}
    {P} →
  _≡_ {A = Outcome} (blamed U) (blamed Z) →
  BlameTrace world-agreement P U →
  BlameTrace world-agreement P Z
blame-trace-result-eq Relation.Binary.PropositionalEquality.refl trace =
  trace

blame-trace-refl :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs} →
  BlameTrace world-agreement N.blame W
blame-trace-refl =
  blame-trace [] world-trace-done ↠-refl
