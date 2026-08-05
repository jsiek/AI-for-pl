module InterpreterAdequacy.proof.ReturnCompletenessAlignment where

-- File Charter:
--   * Aligns a successful direct-interpreter run with any independently given
--     small-step trace to a value.
--   * Uses return soundness and reduction determinism to recover the exact
--     trace, endpoint, world agreement, and value agreement.
--   * Reduces full return completeness to the sole operational obligation of
--     producing some finite successful interpreter index.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Interpreter using
  (StepIndex; Value; World; returned; run)
open import InterpreterAdequacy.RunReturnSoundness using
  (run-return-soundᵢ)
open import InterpreterAdequacy.TraceAgreement
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import NuReduction using (StoreChanges; ↠-refl; ↠-step; _—↠[_]_)
import NuTerms as N
open import proof.DGG.Core.NuReductionDeterminism using
  (target-tail-prefix-value; value-irreducible)

value-traces-deterministic :
  ∀ {M χs ψs V U} →
  M —↠[ χs ] V →
  N.Value V →
  M —↠[ ψs ] U →
  N.Value U →
  (χs ≡ ψs) × (V ≡ U)
value-traces-deterministic M↠V vV M↠U vU
    with target-tail-prefix-value M↠V M↠U vU
value-traces-deterministic M↠V vV M↠U vU
    | [] , ↠-refl , ψs-eq =
  sym (trans ψs-eq (++-identityʳ _)) , refl
value-traces-deterministic M↠V vV M↠U vU
    | (χ ∷ χs) , ↠-step V→L L↠U , ψs-eq =
  ⊥-elim (value-irreducible vV V→L)

returned-run-aligns-traceᵢ :
  ∀ n {M A χs v W V} →
  (image : InterpreterTerm M) →
  (M⊢ : N._∣_∣_⊢_⦂_ zero [] [] M A) →
  (M↠v : M —↠[ χs ] v) →
  (vV : N.Value v) →
  run M n ≡ returned W V →
  Σ[ world-agreement ∈ WorldTraceAgreement W χs ]
    ValueTraceAgreement world-agreement [] V v
returned-run-aligns-traceᵢ n {χs = χs} {v = v}
    image M⊢ M↠v vV result-eq
    with run-return-soundᵢ n image M⊢ result-eq
returned-run-aligns-traceᵢ n {χs = χs} {v = v}
    image M⊢ M↠v vV result-eq
    | ψs , u , world-agreement , M↠u , vU , V-agrees
    with value-traces-deterministic M↠v vV M↠u vU
returned-run-aligns-traceᵢ n {χs = χs} {v = v}
    image M⊢ M↠v vV result-eq
    | .χs , .v , world-agreement , M↠u , vU , V-agrees
    | refl , refl =
  world-agreement , V-agrees

small-step-return-complete-from-runᵢ :
  ∀ {M A χs v} →
  (image : InterpreterTerm M) →
  (M⊢ : N._∣_∣_⊢_⦂_ zero [] [] M A) →
  (M↠v : M —↠[ χs ] v) →
  (vV : N.Value v) →
  (Σ[ n ∈ StepIndex ]
   Σ[ W ∈ World ]
   Σ[ V ∈ Value ] run M n ≡ returned W V) →
  Σ[ n ∈ StepIndex ]
  Σ[ W ∈ World ]
  Σ[ V ∈ Value ]
  Σ[ world-agreement ∈ WorldTraceAgreement W χs ]
    (run M n ≡ returned W V) ×
    ValueTraceAgreement world-agreement [] V v
small-step-return-complete-from-runᵢ image M⊢ M↠v vV
    (n , W , V , result-eq)
    with returned-run-aligns-traceᵢ n image M⊢ M↠v vV result-eq
small-step-return-complete-from-runᵢ image M⊢ M↠v vV
    (n , W , V , result-eq) | world-agreement , V-agrees =
  n , W , V , world-agreement , result-eq , V-agrees
