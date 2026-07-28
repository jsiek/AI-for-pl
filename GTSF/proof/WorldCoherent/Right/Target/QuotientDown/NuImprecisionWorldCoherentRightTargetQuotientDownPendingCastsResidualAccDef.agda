module
  proof.WorldCoherent.Right.Target.QuotientDown.NuImprecisionWorldCoherentRightTargetQuotientDownPendingCastsResidualAccDef
  where

-- File Charter:
--   * Defines the non-inert active-cast residual of the accessibility-indexed
--     target quotient-down pending worker.
--   * Retains the current quotient derivation, widening pair, composition
--     square, compatibility, and ordinary outer administration tail.
--   * Excludes the terminal inert branch, which the worker closes directly
--     with `closeᵀ` before invoking ordinary pending administration.
--   * Contains no implementation, conclusion alias, new relation constructor,
--     postulate, hole, permissive option, or termination bypass.

open import Agda.Builtin.Equality using (_≡_)
import CastImprecisionShape as CastShape
open import Coercions using (Coercion; Inert)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_<_)
open import Data.Product using (_×_; Σ-syntax)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Induction.WellFounded using (Acc)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientImprecisionCompatibility using
  (ReductionClosedQuotientWideningCompatible)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Relation.Nullary using (¬_)
open import Types using (Ty; TyCtx)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  (resultCtx; resultStore; targetTailChanges; weakIndexedResult)
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureDef
  using (pendingAdministrationRank)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.Right.Core.NuImprecisionRightContextAction
  using (applyRightImpCtxChanges)
open import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix
  using (RightOnlyStoreImpPrefix)
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (rightCatchupIndexedResult)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (lineageStore)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using
  ( TargetAdministrationSpine
  ; applyTargetPendingCasts
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightTargetQuotientDownPendingCastsResidualAccᵀ : Set₁
WorldCoherentRightTargetQuotientDownPendingCastsResidualAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L W : Term} {D D′ A B A′ : Ty}
    {u s : Coercion} {cs : List Coercion}
    {u-shape s-shape}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  ¬ Inert s →
  Value (L ⟨ u ⟩) →
  No• (L ⟨ u ⟩) →
  (vW : Value W) →
  No• W →
  Acc _<_ (pendingAdministrationRank vW (s ∷ cs)) →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK
    (applyTargetPendingCasts (W ⟨ s ⟩) cs) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ L ⊑ W ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρ u s D D′ A B →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ s ⦂ s-shape →
  u-shape ；⌊ pB ⌋≋ᵖ qD ； s-shape →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u s qD pB u-shape s-shape →
  TargetAdministrationSpine ρ A pB pA cs →
  Σ[ caught ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = L ⟨ u ⟩}
      {M′ = applyTargetPendingCasts (W ⟨ s ⟩) cs}
      {ρ = ρ} pA ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage caught))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught))))
