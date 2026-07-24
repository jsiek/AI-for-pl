module proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalProof where

-- File Charter:
--   * Implements the world-coherent right-value terminal base case.
--   * Builds the zero-step weak result at the ambient relational-store prefix
--     while preserving the source and target values unchanged.
--   * Uses only focused prefix, typing, result, and lineage infrastructure.
--   * Contains no postulate, hole, incomplete match, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Nat.Properties using (≤-refl)

open import NuReduction using (keep; ↠-refl)
open import NuTerms using (⇑ᵗᵐ; _•)
open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  )
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (right-value-indexed-catchup)
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupSourceBulletTransportDef
  using (RightValueCatchupSourceBulletTransportᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( weak-indexed-result
  ; source-nu-index
  ; weak-step-result
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  ( leftStoreⁱ-prefix-inclusion
  ; rightStoreⁱ-prefix-inclusion
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (weak-step-store-lineage)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using (world-coherent-right-value-indexed-catchup)
open import
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalDef
  using (WorldCoherentRightValueTerminalᵀ)
open import proof.Core.Properties.TypePreservation using (term-weaken)


world-coherent-right-value-terminal-proofᵀ :
  WorldCoherentRightValueTerminalᵀ
world-coherent-right-value-terminal-proofᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {V = V} {V′ = V′} {A = A} {B = B}
    {ρ⁺ = ρ⁺} {p = p}
    prefix coherent exclusive unique wfR vV noV vV′ noV′ V⊑V′ =
  world-coherent-right-value-indexed-catchup
    (right-value-indexed-catchup indexed refl refl vV noV vV′ noV′)
    lineage source-bullet-transport coherent exclusive unique wfR
  where
  source-typing⁺ =
    term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      noV (nu-term-imprecision-source-typing V⊑V′)

  target-typing⁺ =
    term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      noV′ (nu-term-imprecision-target-typing V⊑V′)

  related⁺ =
    allocation-prefixᵀ prefix V⊑V′ source-typing⁺ target-typing⁺

  result =
    weak-step-result
      [] [] V V′ Φ Δᴸ Δᴿ refl refl ρ⁺ A B refl refl
      (λ q → q)
      (λ q → q)
      (λ q → q)
      (λ safe occ q → source-nu-index safe occ q refl)
      p
      ↠-refl
      ↠-refl
      refl
      refl
      related⁺

  transport =
    weak-step-transport (λ noL noL′ L⊑L′ → L⊑L′)

  type-coherence =
    weak-step-type-coherence (λ pC pD → refl) (λ q → refl)

  indexed =
    weak-indexed-result result related⁺ transport type-coherence

  lineage =
    weak-step-store-lineage ρ⁺ rel-store-embedding-reflⁱ prefix-reflⁱ

  source-bullet-transport :
    RightValueCatchupSourceBulletTransportᵀ result
  source-bullet-transport {L = L} {M′ = M′} {C = C} {C′ = C′}
      {q = q} prefix′ okL noL′ L⊢ L⊑L′ =
    allocation-prefixᵀ {ρ = ρ⁺} {M = (⇑ᵗᵐ L) •} {M′ = M′}
      {A = C} {B = C′} {p = q}
      prefix′ L⊑L′ L⊢ target-typing′
    where
    target-typing′ =
      term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix′)
        noL′ (nu-term-imprecision-target-typing L⊑L′)
