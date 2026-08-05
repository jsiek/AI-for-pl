module InterpreterAdequacy.proof.ProxyTraceDecomposition where

-- File Charter:
--   * Decomposes the tail after a function-proxy beta step into input-cast,
--     underlying-application, and output-cast traces.
--   * Eliminates the necessarily reflexive evaluation of the already-valued
--     underlying function.
--   * Records the exact coercion shifts caused by the two earlier phases.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; trans)

import Coercions as C
open import InterpreterAdequacy.proof.ApplicationTraceDecomposition
open import InterpreterAdequacy.proof.CastTraceDecomposition
open import NuReduction
import NuTerms as N
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyCoercions-++)

record ProxyTraceDecomposition
    (base argument : N.Term) (p q : C.Coercion)
    (changes : StoreChanges) (result : N.Term) : Set where
  constructor proxy-trace-decomposition
  field
    input-changes : StoreChanges
    application-changes : StoreChanges
    output-changes : StoreChanges
    input-value : N.Term
    application-value : N.Term
    input-is-value : N.Value input-value
    application-is-value : N.Value application-value
    input-trace :
      (argument N.⟨ p ⟩) —↠[ input-changes ] input-value
    application-trace :
      (applyTerms input-changes base N.· input-value)
        —↠[ application-changes ] application-value
    output-trace :
      (application-value N.⟨
        applyCoercions (input-changes ++ application-changes) q ⟩)
        —↠[ output-changes ] result
    changes-eq :
      changes ≡
        input-changes ++ (application-changes ++ output-changes)

open ProxyTraceDecomposition public

decompose-proxy-tail :
  ∀ {base argument p q changes result} →
  N.Value base →
  ((base N.· (argument N.⟨ p ⟩)) N.⟨ q ⟩)
    —↠[ changes ] result →
  N.Value result →
  ProxyTraceDecomposition base argument p q changes result
decompose-proxy-tail {q = q} vBase trace vResult
    with decompose-cast-value-trace trace vResult
decompose-proxy-tail {q = q} vBase trace vResult
    | cast-trace-decomposition
        operand-changes output-changes application-value
        application-is-value operand-trace output-trace refl
    with decompose-application-value-trace
      operand-trace application-is-value
decompose-proxy-tail {q = q} vBase trace vResult
    | cast-trace-decomposition
        ._ output-changes application-value
        application-is-value operand-trace output-trace refl
    | application-trace-decomposition
        left-changes input-changes application-changes
        function-value input-value function-is-value input-is-value
        left-trace input-trace application-trace refl
    with value-trace-refl vBase left-trace
decompose-proxy-tail {q = q} vBase trace vResult
    | cast-trace-decomposition
        ._ output-changes application-value
        application-is-value operand-trace output-trace refl
    | application-trace-decomposition
        .[] input-changes application-changes
        ._ input-value function-is-value input-is-value
        left-trace input-trace application-trace refl
    | refl , refl =
  proxy-trace-decomposition
    input-changes application-changes output-changes
    input-value application-value input-is-value application-is-value
    input-trace application-trace output-trace
    (++-assoc input-changes application-changes output-changes)
