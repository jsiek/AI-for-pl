module Runtime.InterpreterTypeEnvironmentClosing where

-- File Charter:
--   * Public synchronized type-environment extensions used by `closeValue`.
--   * States paired seal allocation, left abstract binding, and source-only
--     seal allocation at an explicit future allocation scope.
--   * Delegates proofs to a reduction-free private module.

open import Data.List using (_∷_)
open import Data.Nat using (zero)
open import Data.Product using (Σ-syntax)

open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴸᵢ)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped)
open import Types
import proof.InterpreterTypeEnvironmentClosingProof as Proof

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-seal-allocation-realization :
  ∀ {W W′ U U′ Φ θ θ′ A A′ σ σ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  (R≤S : WorldExtension R S) →
  (A~A′ : InterpreterTypeNarrowing A A′) →
  (σ~σ′ : TypeEnvironmentNarrowing S σ σ′) →
  TypeEnvironmentRealization R Φ θ θ′ →
  TypeEnvironmentRealization
    (allocate-both S A~A′ σ~σ′)
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    (seal-name (freshSealName U) ∷ θ)
    (seal-name (freshSealName U′) ∷ θ′)
paired-seal-allocation-realization =
  Proof.paired-seal-allocation-realization

left-abstract-realization :
  ∀ {W W′ Φ θ θ′ X}
    {R : WorldRelation W W′} →
  TypeEnvironmentRealization R Φ θ θ′ →
  TypeEnvironmentRealization R
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    (abstract-name X ∷ θ) θ′
left-abstract-realization =
  Proof.left-abstract-realization

left-dynamic-seal-allocation-realization-at :
  ∀ {W W′ U U′ Φ θ θ′ σ} {allocated-type : Ty}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  (R≤S : WorldExtension R S) →
  (σ-ok : TypeEnvironmentScoped U σ) →
  TypeEnvironmentRealization R Φ θ θ′ →
  TypeEnvironmentRealization
    (allocate-left-dynamic {A = allocated-type} S σ-ok)
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    (seal-name (freshSealName U) ∷ θ) θ′
left-dynamic-seal-allocation-realization-at =
  Proof.left-dynamic-seal-allocation-realization-at

left-dynamic-seal-allocation-realization :
  ∀ {W W′ U U′ Φ θ θ′} {allocated-type : Ty}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  (R≤S : WorldExtension R S) →
  TypeEnvironmentRealization R Φ θ θ′ →
  Σ[ θ-ok ∈ TypeEnvironmentScoped U θ ]
    TypeEnvironmentRealization
      (allocate-left-dynamic {A = allocated-type} S θ-ok)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (seal-name (freshSealName U) ∷ θ) θ′
left-dynamic-seal-allocation-realization =
  Proof.left-dynamic-seal-allocation-realization
