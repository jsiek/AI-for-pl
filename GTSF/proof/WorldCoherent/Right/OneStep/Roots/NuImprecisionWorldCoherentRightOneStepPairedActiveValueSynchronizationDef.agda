module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationDef
  where

-- File Charter:
--   * Defines the exact final-value synchronization cell for paired outer
--     casts when the source cast is active.
--   * Keeps the source non-inert witness, both value/no-bullet facts, exact
--     PairedCast evidence, target root, and full world-coherent outcome.
--   * Contains no implementation, source-inert fallback, quotient case,
--     recursive dispatcher, postulate, hole, or permissive option.

open import Coercions using (Coercion; Inert)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedCast
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ : Set₁
WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ N′ : Term} {A A′ B B′ : Ty}
    {c c′ : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (V ⟨ c ⟩) →
  RuntimeOK (V′ ⟨ c′ ⟩) →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  (Inert c → ⊥) →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ A′ ∶ p →
  V′ ⟨ c′ ⟩ —→ N′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = V ⟨ c ⟩} {N′ = N′}
    {χ = keep} {ρ = ρ} q
