module
  proof.WorldCoherent.Right.Target.QuotientDown.NuImprecisionWorldCoherentRightTargetQuotientDownPendingNuAllocationPathAccDef
  where

-- File Charter:
--   * Defines target-only allocation for a pending runtime `ν ★` whose
--     active `inst` is related through a proof-relevant quotient
--     representative.
--   * Retains both normalized `∀`-permutation paths, the current quotient
--     term relation, widening pair, composition square, reduction-closed
--     compatibility, and typed outer administration spine.
--   * Returns the existing contextual right-value catch-up package after
--     target `bind` and the remaining administration.
--   * Contains no implementation, conclusion alias, ordinary pre-inst edge,
--     new term-imprecision constructor, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_)
import CastImprecisionShape as CastShape
open import Coercions using (Coercion; inst)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_<_)
open import Data.Product using (_×_; Σ-syntax)
open import ForallPermutation using
  (_≈∀_; _∣_⊢_⊑ᵖ_⊣_; quotientᵖ)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Induction.WellFounded using (Acc)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp; rightStoreⁱ)
import NuTerms
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import QuotientImprecisionCompatibility using
  (ReductionClosedQuotientWideningCompatible)
import Types
open import Types using (Ty; TyCtx; `∀)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  (resultCtx; resultStore; targetTailChanges; weakIndexedResult)
open import
  proof.Core.Administration.NuImprecisionAdministrationMeasureDef
  using (pendingAdministrationRank)
open import proof.Core.Permutation.ForallPermutationPath using
  (_≈∀ⁿ_; normalize-forall-permutation)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
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


WorldCoherentRightTargetQuotientDownPendingNuAllocationPathAccᵀ :
  Set₁
WorldCoherentRightTargetQuotientDownPendingNuAllocationPathAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L W : Term}
    {D R R′ C A B A′ : Ty}
    {u s : Coercion} {cs : List Coercion}
    {u-shape inst-shape}
    {source-permutation : D ≈∀ R}
    {representative : Φ ∣ Δᴸ ⊢ R ⊑ R′ ⊣ Δᴿ}
    {target-permutation : R′ ≈∀ `∀ C}
    {pB : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (sourcePath : D ≈∀ⁿ R) →
  (targetPath : R′ ≈∀ⁿ `∀ C) →
  normalize-forall-permutation source-permutation ≡ sourcePath →
  normalize-forall-permutation target-permutation ≡ targetPath →
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
    (applyTargetPendingCasts (NuTerms.ν Types.★ W s) cs) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ L ⊑ W
      ⦂ D ⊑ᵖ `∀ C
      ∶ quotientᵖ
          source-permutation
          representative
          target-permutation →
  QuotientWideningPair Δᴸ Δᴿ ρ
    u (inst B s) D (`∀ C) A B →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ
    inst B s ⦂ inst-shape →
  u-shape ；⌊ pB ⌋≋ᵖ
    quotientᵖ
      source-permutation
      representative
      target-permutation
    ； inst-shape →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u (inst B s)
    (quotientᵖ
      source-permutation
      representative
      target-permutation)
    pB u-shape inst-shape →
  TargetAdministrationSpine ρ A pB pA cs →
  Σ[ caught ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = L ⟨ u ⟩}
      {M′ =
        applyTargetPendingCasts
          (NuTerms.ν Types.★ W s) cs}
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
