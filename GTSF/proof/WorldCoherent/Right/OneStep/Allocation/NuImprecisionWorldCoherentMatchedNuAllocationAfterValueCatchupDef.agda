module
  proof.WorldCoherent.Right.OneStep.Allocation.NuImprecisionWorldCoherentMatchedNuAllocationAfterValueCatchupDef
  where

-- File Charter:
--   * States matched polymorphic allocation after left catch-up has already
--     reached a value.
--   * Couples the indexed result with its store lineage and final
--     world/context invariants.
--   * Keeps the target-allocation root proof independent of monolithic
--     allocation and simulation implementations.

open import Coercions using (Coercion)
open import Conversion using (RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)

open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; _∣_⊢_⊑_⊣_
  ; ⇑ᵢ
  )
open import NuReduction using (bind)
open import NuTermImprecision using (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import Types using
  ( Ty
  ; TyCtx
  ; ⇑ᵗ
  ; ⟰ᵗ
  )
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (∀ᵢᶜ; ⊑-lift∀ᵢ)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftCatchupIndexedAllResult
  ; catchupIndexedAllResult
  ; resultCtx
  ; resultStore
  ; sourceResult
  ; weakIndexedResult
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (WeakOneStepStoreLineage)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


WorldCoherentMatchedNuAllocationAfterValueCatchupᵀ : Set₁
WorldCoherentMatchedNuAllocationAfterValueCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {A A′ B B′ C C′ : Ty} {N V′ : Term}
    {s s′ : Coercion} {μ μ′}
    {q : ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  RevealConversion μ′ (suc Δᴿ)
    ((zero , ⇑ᵗ A′) ∷ ⟰ᵗ (rightStoreⁱ ρ))
    zero (⇑ᵗ A′) s′ C′ (⇑ᵗ B′) →
  (pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (A⇑⊑A′⇑ : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  (pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  q
    [ zero ↦ ⇑ᵗ A
    ⊑⟨ A⇑⊑A′⇑ ⟩
    ⇑ᵗ A′ ↤ zero ]ᴾ
    ⊑-lift∀ᵢ pB →
  (vV′ : Value V′) →
  (noV′ : No• V′) →
  (catchup : LeftCatchupIndexedAllResult
    {N = N} {V′ = V′} {ρ = ρ} q) →
  (vW : Value
    (sourceResult
      (weakIndexedResult (catchupIndexedAllResult catchup)))) →
  (noW : No•
    (sourceResult
      (weakIndexedResult (catchupIndexedAllResult catchup)))) →
  WeakOneStepStoreLineage
    (weakIndexedResult (catchupIndexedAllResult catchup)) →
  WorldCoherent
    (resultStore
      (weakIndexedResult (catchupIndexedAllResult catchup))) →
  SourceNameExclusive
    (resultCtx
      (weakIndexedResult (catchupIndexedAllResult catchup))) →
  AssumptionMembershipUnique
    (resultCtx
      (weakIndexedResult (catchupIndexedAllResult catchup))) →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = ν A N s} {N′ = ((⇑ᵗᵐ V′) •) ⟨ s′ ⟩}
    {χ = bind A′} {ρ = ρ} pB
