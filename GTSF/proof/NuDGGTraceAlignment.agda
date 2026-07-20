module proof.NuDGGTraceAlignment where

-- File Charter:
--   * Connects weak one-step simulation results to terminal target traces.
--   * Aligns each administrative target tail with an observed trace to a
--     value or blame, and preserves the sound source-blame alternative.
--   * Depends on Nu reduction determinism and the weak simulation interface.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (_++_)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import NuReduction using (_—↠[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; Value; blame)
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepOutcome
  ; WeakOneStepResult
  ; outcome-related
  ; outcome-source-blame
  )
open WeakOneStepResult using
  (targetResult; targetTail; targetTailChanges)
open import proof.NuReductionDeterminism using
  (target-tail-prefix-blame; target-tail-prefix-value)


weak-result-target-prefix-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ ψs V}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result : WeakOneStepResult ρ M N′ A B χ) →
  N′ —↠[ ψs ] V →
  Value V →
  ∃[ θs ]
    ((targetResult result —↠[ θs ] V) ×
      (ψs ≡ targetTailChanges result ++ θs))
weak-result-target-prefix-valueᵀ result N′↠V vV =
  target-tail-prefix-value (targetTail result) N′↠V vV

weak-result-target-prefix-blameᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ ψs}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  (result : WeakOneStepResult ρ M N′ A B χ) →
  N′ —↠[ ψs ] blame →
  ∃[ θs ]
    ((targetResult result —↠[ θs ] blame) ×
      (ψs ≡ targetTailChanges result ++ θs))
weak-result-target-prefix-blameᵀ result N′↠blame =
  target-tail-prefix-blame (targetTail result) N′↠blame


weak-outcome-target-value-alignedᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ ψs V}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WeakOneStepOutcome ρ M N′ A B χ →
  N′ —↠[ ψs ] V →
  Value V →
  (Σ[ result ∈ WeakOneStepResult ρ M N′ A B χ ]
    ∃[ θs ]
      ((targetResult result —↠[ θs ] V) ×
        (ψs ≡ targetTailChanges result ++ θs)))
  ⊎ ∃[ χs ] (M —↠[ χs ] blame)
weak-outcome-target-value-alignedᵀ
    (outcome-related result transport coherence) N′↠V vV
  with weak-result-target-prefix-valueᵀ result N′↠V vV
weak-outcome-target-value-alignedᵀ
    (outcome-related result transport coherence) N′↠V vV
  | θs , result↠V , trace-eq =
    inj₁ (result , θs , result↠V , trace-eq)
weak-outcome-target-value-alignedᵀ
    (outcome-source-blame {χs = χs} M↠blame) N′↠V vV =
  inj₂ (χs , M↠blame)

weak-outcome-target-blame-alignedᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A B χ ψs}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  WeakOneStepOutcome ρ M N′ A B χ →
  N′ —↠[ ψs ] blame →
  (Σ[ result ∈ WeakOneStepResult ρ M N′ A B χ ]
    ∃[ θs ]
      ((targetResult result —↠[ θs ] blame) ×
        (ψs ≡ targetTailChanges result ++ θs)))
  ⊎ ∃[ χs ] (M —↠[ χs ] blame)
weak-outcome-target-blame-alignedᵀ
    (outcome-related result transport coherence) N′↠blame
  with weak-result-target-prefix-blameᵀ result N′↠blame
weak-outcome-target-blame-alignedᵀ
    (outcome-related result transport coherence) N′↠blame
  | θs , result↠blame , trace-eq =
    inj₁ (result , θs , result↠blame , trace-eq)
weak-outcome-target-blame-alignedᵀ
    (outcome-source-blame {χs = χs} M↠blame) N′↠blame =
  inj₂ (χs , M↠blame)
