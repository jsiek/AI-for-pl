module proof.NuImprecisionWorldCoherentResultDef where

-- File Charter:
--   * Defines weak simulation outcomes that preserve the world/store-name
--     coherence invariant on every continuing related branch.
--   * Wraps the generic result algebra without importing a simulation
--     implementation or recursive dispatcher.
--   * Gives continuing results explicit final-world and context invariants.

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (_—↠[_]_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (blame)
open import proof.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; WeakOneStepIndexedResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; catchupIndexedResult
  ; resultCtx
  ; resultLeftCtx
  ; resultStore
  ; weakIndexedResult
  )
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  (WeakOneStepStoreLineage)


data WorldCoherentWeakOneStepIndexedOutcome
    {Φ Δᴸ Δᴿ M N′ A B χ}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  world-indexed-outcome-related :
    (result : WeakOneStepIndexedResult
      {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p) →
    WeakOneStepTransport (weakIndexedResult result) →
    WeakOneStepTypeCoherence (weakIndexedResult result) →
    WorldCoherent (resultStore (weakIndexedResult result)) →
    SourceNameExclusive (resultCtx (weakIndexedResult result)) →
    WorldCoherentWeakOneStepIndexedOutcome p

  world-indexed-outcome-source-blame : ∀ {χs} →
    M —↠[ χs ] blame →
    WorldCoherentWeakOneStepIndexedOutcome p


record WorldCoherentLeftCatchupIndexedResult
    {Φ Δᴸ Δᴿ N V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  constructor world-coherent-left-indexed-catchup
  field
    worldCatchupResult :
      LeftCatchupIndexedResult
        {N = N} {V′ = V′} {ρ = ρ} p
    worldCatchupStoreLineage :
      WeakOneStepStoreLineage
        (weakIndexedResult
          (catchupIndexedResult worldCatchupResult))
    worldCatchupCoherence :
      WorldCoherent
        (resultStore
          (weakIndexedResult
            (catchupIndexedResult worldCatchupResult)))
    worldCatchupSourceNameExclusive :
      SourceNameExclusive
        (resultCtx
          (weakIndexedResult
            (catchupIndexedResult worldCatchupResult)))
    worldCatchupSourceStoreWf :
      StoreWf
        (resultLeftCtx
          (weakIndexedResult
            (catchupIndexedResult worldCatchupResult)))
        (leftStoreⁱ
          (resultStore
            (weakIndexedResult
              (catchupIndexedResult worldCatchupResult))))

open WorldCoherentLeftCatchupIndexedResult public
