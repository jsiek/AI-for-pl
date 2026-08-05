module InterpreterAdequacy.proof.ApplicationTraceDecomposition where

-- File Charter:
--   * Decomposes a terminating application trace into left evaluation, right
--     evaluation, and active-application phases.
--   * Accounts for store-change renaming of the suspended argument and the
--     already evaluated function value.
--   * Uses only determinism/value irreducibility; it runs no interpreter.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import NuReduction
import NuTerms as N
import Coercions as C
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-Value)
open import proof.DGG.Core.NuReductionDeterminism using
  (blame-irreducible; value-irreducible)

record ApplicationTraceDecomposition
    (L M : N.Term) (χs : StoreChanges) (z : N.Term) : Set where
  constructor application-trace-decomposition
  field
    left-changes : StoreChanges
    right-changes : StoreChanges
    active-changes : StoreChanges
    function-value : N.Term
    argument-value : N.Term
    function-is-value : N.Value function-value
    argument-is-value : N.Value argument-value
    left-trace : L —↠[ left-changes ] function-value
    right-trace :
      applyTerms left-changes M —↠[ right-changes ] argument-value
    active-trace :
      (applyTerms right-changes function-value N.· argument-value)
        —↠[ active-changes ] z
    changes-eq :
      χs ≡ left-changes ++ (right-changes ++ active-changes)

open ApplicationTraceDecomposition public

value-trace-refl :
  ∀ {V χs U} →
  N.Value V →
  V —↠[ χs ] U →
  (χs ≡ []) × (U ≡ V)
value-trace-refl vV ↠-refl = refl , refl
value-trace-refl vV (↠-step V→L L↠U) =
  ⊥-elim (value-irreducible vV V→L)

blame-does-not-reach-value :
  ∀ {χs V} →
  N.blame —↠[ χs ] V →
  N.Value V →
  ⊥
blame-does-not-reach-value ↠-refl ()
blame-does-not-reach-value (↠-step blame→L L↠V) vV =
  ⊥-elim (blame-irreducible blame→L)

prepend-left-step :
  ∀ {χ χs L L′ M z} →
  L —→[ χ ] L′ →
  ApplicationTraceDecomposition L′ (applyTerm χ M) χs z →
  ApplicationTraceDecomposition L M (χ ∷ χs) z
prepend-left-step {χ = χ} {M = M} L→L′
    (application-trace-decomposition
      χL χM χA f u vf vu L′↠f M↠u A↠z refl) =
  application-trace-decomposition
    (χ ∷ χL) χM χA f u vf vu
    (↠-step L→L′ L′↠f)
    M↠u A↠z refl

prepend-right-step :
  ∀ {χ χs L M M′ z} →
  (vL : N.Value L) →
  M —→[ χ ] M′ →
  ApplicationTraceDecomposition (applyTerm χ L) M′ χs z →
  ApplicationTraceDecomposition L M (χ ∷ χs) z
prepend-right-step {χ = χ} {L = L} vL M→M′
    decomposition@(application-trace-decomposition
      χL χM χA f u vf vu shifted-L↠f M′↠u A↠z changes-eq)
    with value-trace-refl
      (apply-term-value χ vL) shifted-L↠f
  where
  apply-term-value :
    ∀ χ {V} → N.Value V → N.Value (applyTerm χ V)
  apply-term-value keep vV = vV
  apply-term-value (bind A) vV = renameᵗᵐ-preserves-Value _ vV
prepend-right-step {χ = χ} {L = L} vL M→M′
    (application-trace-decomposition
      .[] χM χA .(applyTerm χ L) u vf vu
      shifted-L↠f M′↠u A↠z changes-eq)
    | refl , refl =
  application-trace-decomposition
    [] (χ ∷ χM) χA L u vL vu
    ↠-refl (↠-step M→M′ M′↠u) A↠z
    (cong (χ ∷_) changes-eq)

decompose-application-value-trace :
  ∀ {L M χs z} →
  (L N.· M) —↠[ χs ] z →
  N.Value z →
  ApplicationTraceDecomposition L M χs z
decompose-application-value-trace ↠-refl ()
decompose-application-value-trace
    (↠-step (pure-step (β vM)) tail) vz =
  application-trace-decomposition
    [] [] (keep ∷ _) (N.ƛ _) _ (N.ƛ _) vM
    ↠-refl ↠-refl
    (↠-step (pure-step (β vM)) tail) refl
decompose-application-value-trace
    (↠-step (pure-step
      (β-↦ {V = V} {W = W} {p = p} {q = q} vV vW)) tail) vz =
  application-trace-decomposition
    [] [] (keep ∷ _) (V N.⟨ p C.↦ q ⟩) W
    (vV N.⟨ _ C.↦ _ ⟩) vW
    ↠-refl ↠-refl
    (↠-step (pure-step (β-↦ vV vW)) tail) refl
decompose-application-value-trace
    (↠-step (pure-step blame-·₁) tail) vz =
  ⊥-elim (blame-does-not-reach-value tail vz)
decompose-application-value-trace
    (↠-step (pure-step (blame-·₂ vV)) tail) vz =
  ⊥-elim (blame-does-not-reach-value tail vz)
decompose-application-value-trace
    (↠-step (ξ-·₁ L→L′ shiftM) tail) vz =
  prepend-left-step L→L′
    (decompose-application-value-trace tail vz)
decompose-application-value-trace
    (↠-step (ξ-·₂ vL shiftL M→M′) tail) vz =
  prepend-right-step vL M→M′
    (decompose-application-value-trace tail vz)
