module InterpreterAdequacy.proof.InitialTraceAgreement where

-- File Charter:
--   * Constructs the canonical trace agreement for a closed, well-typed
--     source program in the empty interpreter world and environments.
--   * Uses typing only to discharge identity substitution on the closed term.
--   * Contains no interpreter recursion or reduction argument.

open import Data.List using ([])
open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  ( empty-world-trace-agreement
  ; empty-type-environment-trace-agreement
  ; empty-environment-trace-agreement
  )
import NuTerms as N
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-id; subst-closedᵐ; typing-closedᵐ)

initial-term-trace-agreement :
  ∀ {M A} →
  N._∣_∣_⊢_⦂_ zero [] [] M A →
  TermTraceAgreement empty-world-trace-agreement [] [] [] M M
initial-term-trace-agreement {M = M} M⊢ =
  term-trace-agreement (λ X → X) []
    empty-type-environment-trace-agreement
    empty-environment-trace-agreement
    (sym
      (trans
        (cong (N.substˣᵐ (environmentSubstitution []))
          (renameᵗᵐ-id M))
        (subst-closedᵐ (typing-closedᵐ M⊢)
          (environmentSubstitution []))))
