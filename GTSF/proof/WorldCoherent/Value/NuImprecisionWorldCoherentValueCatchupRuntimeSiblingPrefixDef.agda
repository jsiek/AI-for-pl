module
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupRuntimeSiblingPrefixDef
  where

-- File Charter:
--   * Defines ambient and prefix entry contracts for left-value catch-up with
--     lockstep transport of one independent source-no-bullet, target-runtime
--     sibling relation.
--   * Returns the ordinary canonical caught result together with the sibling
--     relation at that exact result's final world and transported index.
--   * Keeps the dependent conclusion inline instead of introducing a result
--     wrapper or an aggregate theorem over opaque final-world invariants.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using ([])
open import Data.Product using (Σ-syntax)

open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; keep
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( catchupIndexedResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
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
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  )


WorldCoherentLeftValueCatchupRuntimeSiblingAmbientᵀ : Set₁
WorldCoherentLeftValueCatchupRuntimeSiblingAmbientᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ R R′ : Term} {A A′ C C′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
  RuntimeOK L →
  Value L′ →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ A ⊑ A′ ∶ p →
  No• R →
  RuntimeOK R′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ []
    ⊢ᴺ R ⊑ R′ ⦂ C ⊑ C′ ∶ q →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = L} {V′ = L′} {ρ = ρ⁺} p ]
    let result =
          weakIndexedResult
            (catchupIndexedResult (worldCatchupResult caught))
    in
    resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ applyTerms (sourceChanges result) R
        ⊑ applyTerms (targetTailChanges result) (applyTerm keep R′)
      ⦂ applyTys (sourceChanges result) C
        ⊑ applyTys (targetTailChanges result) (applyTy keep C′)
      ∶ transportType result q


WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ : Set₁
WorldCoherentLeftValueCatchupRuntimeSiblingPrefixᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {L L′ R R′ : Term} {A A′ C C′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK L →
  Value L′ →
  No• L′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ L ⊑ L′ ⦂ A ⊑ A′ ∶ p →
  No• R →
  RuntimeOK R′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ R ⊑ R′ ⦂ C ⊑ C′ ∶ q →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ R ⦂ C →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ R′ ⦂ C′ →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = L} {V′ = L′} {ρ = ρ} p ]
    let result =
          weakIndexedResult
            (catchupIndexedResult (worldCatchupResult caught))
    in
    resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ applyTerms (sourceChanges result) R
        ⊑ applyTerms (targetTailChanges result) (applyTerm keep R′)
      ⦂ applyTys (sourceChanges result) C
        ⊑ applyTys (targetTailChanges result) (applyTy keep C′)
      ∶ transportType result q
