module
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportDef
  where

-- File Charter:
--   * Defines transport of a runtime source and no-bullet target through a
--     completed world-coherent right-value catch-up.
--   * Returns the transported quotient relation directly, without another
--     result carrier or proof implementation.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using ([])

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyTerm; applyTerms; applyTy; applyTys; keep)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using
  (_∣_∣_⊢_⦂_)
open import Types using
  (Ty; TyCtx)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  )


WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ : Set₁
WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {V N′ M M′ : Term} {A A′ C C′ : Ty}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RuntimeOK M →
  No• M′ →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ M ⦂ C →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ q →
  (caught : WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = N′} {ρ = ρ⁺} p) →
  resultCtx
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult caught)))
    ∣ resultLeftCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
    ∣ resultRightCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
    ∣ resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
    ∣ []
    ⊢ᴺ applyTerms
          (sourceChanges
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
          M
      ⊑ applyTerms
          (targetTailChanges
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
          (applyTerm keep M′)
    ⦂ applyTys
          (sourceChanges
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
          C
      ⊑ applyTys
          (targetTailChanges
            (weakIndexedResult
              (rightCatchupIndexedResult
                (worldRightCatchupResult caught))))
          (applyTy keep C′)
    ∶ transportType
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
        q
