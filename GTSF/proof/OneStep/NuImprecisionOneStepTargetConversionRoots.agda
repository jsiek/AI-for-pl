{-# OPTIONS --allow-unsolved-metas #-}

module proof.OneStep.NuImprecisionOneStepTargetConversionRoots where

-- File Charter:
--   * Freezes the two root-only target-conversion outcomes required by the
--     indexed one-step dispatcher.
--   * Excludes ξ-⟨⟩, which is handled by the target-conversion frame
--     module.
--   * Each helper owns exhaustive inversion of the corresponding ordinary
--     conversion redex while preserving the explicit result index and its
--     right-endpoint replacement evidence.
--   * The reveal-unseal branch remains blocked on source value catch-up and
--     world coherence, which this root-only contract does not provide.

open import Conversion using
  ( ConcealConversion
  ; RevealConversion
  ; conceal-id-base
  ; conceal-id-var
  ; conceal-id-★
  ; reveal-id-base
  ; reveal-id-var
  ; reveal-id-★
  ; reveal-unseal
  )
open import Data.List using ([])
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( blame-⟨⟩
  ; keep
  ; seal-unseal
  ; β-id
  ; _—→_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Atom; ＇_; ‵_; ★)
open import proof.Core.Properties.NuRuntimeProperties using (runtime-⟨⟩)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  (WeakOneStepIndexedOutcome)
open import proof.OneStep.NuImprecisionOneStepRelated using
  (weak-one-step-indexed-outcome-relatedᵀ)
open import proof.OneStep.NuImprecisionAtomicTargetReindex using
  (atomic-target-value-reindexᵀ)
open import proof.OneStep.NuImprecisionOneStepTargetBlameRoots using
  (weak-one-step-target-blame-indexed-outcomeᵀ)


weak-one-step-target-atomic-identity-root-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M V A B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  Atom B →
  RuntimeOK M →
  RuntimeOK V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V ⦂ A ⊑ B ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  Value V →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = V} {χ = keep} {ρ = ρ} q
weak-one-step-target-atomic-identity-root-outcomeᵀ
    atom okM okV M⊑V q vV =
  weak-one-step-indexed-outcome-relatedᵀ
    (atomic-target-value-reindexᵀ atom vV M⊑V q)


weak-one-step-target-reveal-conversion-root-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ N′ A A′ B′ c′ μ′ β X′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK (M′ ⟨ c′ ⟩) →
  RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
    β X′ c′ A′ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  p [ β ↦ X′ ]ᴿ q →
  M′ ⟨ c′ ⟩ —→ N′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q
weak-one-step-target-reveal-conversion-root-outcomeᵀ
    wf okM okM′ (reveal-id-var hY ok) M⊑M′ q replace
    (β-id vV) =
  weak-one-step-target-atomic-identity-root-outcomeᵀ
    (＇ _) okM (runtime-⟨⟩ okM′) M⊑M′ q vV
weak-one-step-target-reveal-conversion-root-outcomeᵀ
    wf okM okM′ reveal-id-base M⊑M′ q replace (β-id vV) =
  weak-one-step-target-atomic-identity-root-outcomeᵀ
    (‵ _) okM (runtime-⟨⟩ okM′) M⊑M′ q vV
weak-one-step-target-reveal-conversion-root-outcomeᵀ
    wf okM okM′ reveal-id-★ M⊑M′ q replace (β-id vV) =
  weak-one-step-target-atomic-identity-root-outcomeᵀ
    ★ okM (runtime-⟨⟩ okM′) M⊑M′ q vV
weak-one-step-target-reveal-conversion-root-outcomeᵀ
    wf okM okM′ (reveal-unseal hX′ β∈Σ ok) M⊑M′ q replace
    (seal-unseal vV) =
  -- `replace` transports the type index, but target seal cancellation first
  -- needs a source value related to the target seal.  Producing that value,
  -- and canceling source-only seals encountered on the way, requires the
  -- world-coherent value-catchup invariants absent from this contract.
  {!!}
weak-one-step-target-reveal-conversion-root-outcomeᵀ
    wf okM okM′ c↑ M⊑blame q replace blame-⟨⟩ =
  weak-one-step-target-blame-indexed-outcomeᵀ okM M⊑blame q


weak-one-step-target-conceal-conversion-root-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ N′ A A′ B′ c′ μ′ β X′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK (M′ ⟨ c′ ⟩) →
  ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
    β X′ c′ A′ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  q [ β ↦ X′ ]ᴿ p →
  M′ ⟨ c′ ⟩ —→ N′ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = keep} {ρ = ρ} q
weak-one-step-target-conceal-conversion-root-outcomeᵀ
    wf okM okM′ (conceal-id-var hY ok) M⊑M′ q replace
    (β-id vV) =
  weak-one-step-target-atomic-identity-root-outcomeᵀ
    (＇ _) okM (runtime-⟨⟩ okM′) M⊑M′ q vV
weak-one-step-target-conceal-conversion-root-outcomeᵀ
    wf okM okM′ conceal-id-base M⊑M′ q replace (β-id vV) =
  weak-one-step-target-atomic-identity-root-outcomeᵀ
    (‵ _) okM (runtime-⟨⟩ okM′) M⊑M′ q vV
weak-one-step-target-conceal-conversion-root-outcomeᵀ
    wf okM okM′ conceal-id-★ M⊑M′ q replace (β-id vV) =
  weak-one-step-target-atomic-identity-root-outcomeᵀ
    ★ okM (runtime-⟨⟩ okM′) M⊑M′ q vV
weak-one-step-target-conceal-conversion-root-outcomeᵀ
    wf okM okM′ c↓ M⊑blame q replace blame-⟨⟩ =
  weak-one-step-target-blame-indexed-outcomeᵀ okM M⊑blame q
