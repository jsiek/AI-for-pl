module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownNuAllocationResidualAccDef
  where

-- File Charter:
--   * Defines the quotient-specific allocation leaf straddling the active
--     target `β-inst` step below one live
--     `closeᵀ (paired-downᵀ ...)` boundary.
--   * Retains the physical quotient endpoints, both composition squares,
--     both compatibility witnesses, and the keep-only trace from the
--     original target boundary to an explicit pending `inst` head.
--   * Exposes the ordinary post-instantiation index and its typed outer
--     administration spine; the active `inst` is not part of that spine.
--   * Requires the source double cast to be a value, separating target-only
--     allocation from source synchronization and catch-up.
--   * Returns the existing world-coherent weak outcome directly, without an
--     ordinary pre-inst edge, result alias, QTI constructor, postulate, hole,
--     permissive option, compatibility wrapper, or termination bypass.

open import Agda.Builtin.Equality using (_≡_)
import CastImprecisionShape as CastShape
open import Coercions using (Coercion; inst)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (_<_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Induction.WellFounded using (Acc)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  (StoreChanges; keep; _—↠[_]_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
import NuTerms
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import QuotientImprecisionCompatibility using
  ( ReductionClosedQuotientWideningCompatible
  ; QuotientNarrowingEliminationCompatible
  )
import Types
open import Types using (Ty; TyCtx)
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
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using
  ( TargetAdministrationSpine
  ; applyTargetPendingCasts
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveSynchronizationDef
  using (QuotientDownMode; quotient-down-mode)


WorldCoherentRightOneStepQuotientDownNuAllocationResidualAccᵀ :
  Set₁
WorldCoherentRightOneStepQuotientDownNuAllocationResidualAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ W : Term} {C C′ D D′ A A′ B : Ty}
    {d d′ u u′ s : Coercion} {cs : List Coercion}
    {χs : StoreChanges}
    {d-shape d′-shape u-shape u′-shape}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (down-mode : QuotientDownMode) →
  (vV : Value V) →
  No• V →
  (vV′ : Value V′) →
  No• V′ →
  (vW : Value W) →
  No• W →
  Value ((V ⟨ d ⟩) ⟨ u ⟩) →
  Acc _<_ (pendingAdministrationRank vW (s ∷ cs)) →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((V ⟨ d ⟩) ⟨ u ⟩) →
  RuntimeOK ((V′ ⟨ d′ ⟩) ⟨ u′ ⟩) →
  RuntimeOK
    (applyTargetPendingCasts (NuTerms.ν Types.★ W s) cs) →
  quotient-down-mode down-mode ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ d ∶ C ⊒ D →
  CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
  quotient-down-mode down-mode ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ d′ ∶ C′ ⊒ D′ →
  CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ C ⊑ C′ ∶ pC →
  d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
  QuotientNarrowingEliminationCompatible
    Φ Δᴸ Δᴿ d d′ pC qD d-shape d′-shape →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
  u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u u′ qD pA u-shape u′-shape →
  TargetAdministrationSpine ρ A pB pA cs →
  ((V′ ⟨ d′ ⟩) ⟨ u′ ⟩)
    —↠[ keep ∷ χs ]
      applyTargetPendingCasts W (inst B s ∷ cs) →
  All (λ χ → χ ≡ keep) χs →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (V ⟨ d ⟩) ⟨ u ⟩}
    {N′ = applyTargetPendingCasts (NuTerms.ν Types.★ W s) cs}
    {χ = keep} {ρ = ρ} pA
