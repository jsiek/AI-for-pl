module proof.NuImprecisionWorldCoherentRightCatchupResultDef where

-- File Charter:
--   * Adds the recursive world and store invariants to right-value catch-up.
--   * Retains relational-store lineage and target-store well-formedness for
--     recursive frame, binder, and allocation cases.
--   * Contains no implementation, postulate, hole, or permissive option.

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.NuImprecisionRightValueCatchupResultDef using
  ( RightValueCatchupIndexedResult
  ; rightCatchupIndexedResult
  )
open import
  proof.NuImprecisionRightValueCatchupSourceBulletTransportDef
  using (RightValueCatchupSourceBulletTransportᵀ)
open import proof.NuImprecisionSimulationResultDef using
  ( resultCtx
  ; resultRightCtx
  ; resultStore
  ; weakIndexedResult
  )
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  (WeakOneStepStoreLineage)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


record WorldCoherentRightValueCatchupIndexedResult
    {Φ Δᴸ Δᴿ V M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  constructor world-coherent-right-value-indexed-catchup
  field
    worldRightCatchupResult :
      RightValueCatchupIndexedResult
        {V = V} {M′ = M′} {ρ = ρ} p

    worldRightCatchupStoreLineage :
      WeakOneStepStoreLineage
        (weakIndexedResult
          (rightCatchupIndexedResult worldRightCatchupResult))

    worldRightCatchupSourceBulletTransport :
      RightValueCatchupSourceBulletTransportᵀ
        (weakIndexedResult
          (rightCatchupIndexedResult worldRightCatchupResult))

    worldRightCatchupCoherence :
      WorldCoherent
        (resultStore
          (weakIndexedResult
            (rightCatchupIndexedResult worldRightCatchupResult)))

    worldRightCatchupSourceNameExclusive :
      SourceNameExclusive
        (resultCtx
          (weakIndexedResult
            (rightCatchupIndexedResult worldRightCatchupResult)))

    worldRightCatchupAssumptionMembershipUnique :
      AssumptionMembershipUnique
        (resultCtx
          (weakIndexedResult
            (rightCatchupIndexedResult worldRightCatchupResult)))

    worldRightCatchupTargetStoreWf :
      StoreWf
        (resultRightCtx
          (weakIndexedResult
            (rightCatchupIndexedResult worldRightCatchupResult)))
        (rightStoreⁱ
          (resultStore
            (weakIndexedResult
              (rightCatchupIndexedResult worldRightCatchupResult))))

open WorldCoherentRightValueCatchupIndexedResult public
