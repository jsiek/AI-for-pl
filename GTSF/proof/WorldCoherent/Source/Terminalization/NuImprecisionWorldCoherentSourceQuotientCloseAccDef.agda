module
  proof.WorldCoherent.Source.Terminalization.NuImprecisionWorldCoherentSourceQuotientCloseAccDef
  where

-- File Charter:
--   * Defines accessibility-ranked source terminalization of one live
--     quotient-closing narrowing/widening pair.
--   * Always preserves one independent runtime sibling, so ordinary and
--     runtime-sibling value catch-up share one semantic worker.
--   * Keeps the proof-relevant quotient edge and its complete widening
--     quartet explicit at the source-administration boundary.
--   * Uses the source-administration rank only as private recursion control.
--   * Contains no implementation, continuation alias, result wrapper,
--     postulate, hole, permissive option, or termination bypass.

import CastImprecisionShape as CastShape
open import Coercions using (Coercion; Inert)
open import Data.List using ([]; _∷_)
open import Data.Nat using (_<_)
open import Data.Product using (Σ-syntax)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Induction.WellFounded using (Acc)
open import NuReduction using
  (applyTerm; applyTerms; applyTy; applyTys; keep)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp; leftStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientImprecisionCompatibility using
  (ReductionClosedQuotientWideningCompatible)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty; TyCtx)
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
  proof.Source.Administration.NuImprecisionSourceAdministrationState
  using (casts; sourceAdministrationRank)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  )


WorldCoherentSourceQuotientCloseAccᵀ : Set₁
WorldCoherentSourceQuotientCloseAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ R R′ : Term}
    {D D′ A A′ E E′ : Ty}
    {d d′ u u′ : Coercion}
    {u-shape u′-shape}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ} →
  (vV : Value V) →
  No• V →
  Acc _<_
    (sourceAdministrationRank vV
      (casts (d ∷ u ∷ []))) →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK ((V ⟨ d ⟩) ⟨ u ⟩) →
  Value V′ →
  No• V′ →
  Inert d′ →
  Inert u′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⟨ d ⟩ ⊑ V′ ⟨ d′ ⟩
      ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρ
    u u′ D D′ A A′ →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
  u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u u′ qD pA u-shape u′-shape →
  No• R →
  RuntimeOK R′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ R ⊑ R′ ⦂ E ⊑ E′ ∶ r →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = (V ⟨ d ⟩) ⟨ u ⟩}
      {V′ = (V′ ⟨ d′ ⟩) ⟨ u′ ⟩}
      {ρ = ρ} pA ]
    let result =
          weakIndexedResult
            (catchupIndexedResult
              (worldCatchupResult caught))
    in
    resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ applyTerms (sourceChanges result) R
        ⊑ applyTerms (targetTailChanges result)
            (applyTerm keep R′)
      ⦂ applyTys (sourceChanges result) E
        ⊑ applyTys (targetTailChanges result)
            (applyTy keep E′)
      ∶ transportType result r
