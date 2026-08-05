module InterpreterAdequacy.proof.BetaReification where

-- File Charter:
--   * Identifies small-step beta substitution with extending an interpreter
--     environment by the argument value.
--   * Is the single substitution-fusion boundary used by application
--     soundness; callers do not manipulate nested substitutions directly.
--   * Contains no interpreter recursion and constructs no reduction step.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; _∷_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import InterpreterAdequacy.TraceAgreement using
  (environmentSubstitution)
open import InterpreterAdequacy.proof.SyntaxReification using
  (substˣᵐ-cong)
open import InterpreterAdequacy.proof.TermSubstitutionComposition using
  ( _⨟ˢ_
  ; subst-after-rename
  ; substˣᵐ-compose
  ; substˣᵐ-identity
  )
import NuTerms as N
open import Types using (Renameᵗ)

beta-environment-compose :
  ∀ u vs x →
  ((N.extˢˣ (environmentSubstitution vs))
    ⨟ˢ N.singleEnv u) x ≡
  environmentSubstitution (u ∷ vs) x
beta-environment-compose u vs zero = refl
beta-environment-compose u vs (suc x) =
  trans
    (subst-after-rename (N.singleEnv u) suc
      (environmentSubstitution vs x))
    (trans
      (substˣᵐ-cong (λ y → refl) (environmentSubstitution vs x))
      (substˣᵐ-identity (environmentSubstitution vs x)))

beta-reification :
  ∀ {M M′} τ vs u →
  M′ ≡
    N.substˣᵐ (N.extˢˣ (environmentSubstitution vs))
      (N.renameᵗᵐ τ M) →
  M′ N.[ u ] ≡
    N.substˣᵐ (environmentSubstitution (u ∷ vs))
      (N.renameᵗᵐ τ M)
beta-reification {M = M} τ vs u reification =
  trans
    (cong (λ body → body N.[ u ]) reification)
    (trans
      (substˣᵐ-compose
        (N.extˢˣ (environmentSubstitution vs))
        (N.singleEnv u) (N.renameᵗᵐ τ M))
      (substˣᵐ-cong (beta-environment-compose u vs)
        (N.renameᵗᵐ τ M)))
