module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownValueAccDef
  where

-- File Charter:
--   * Defines the private accessibility-indexed value kernel for one active
--     target root inside a live `closeᵀ (paired-downᵀ ...)` boundary.
--   * Starts after ordinary body catch-up, so both bodies are values at one
--     exact coherent world and no store-prefix transport remains.
--   * Measures the target down/up pending spine directly and retains both
--     quotient composition squares and compatibility witnesses.
--   * Contains no implementation, public unranked wrapper, frame recursion,
--     application case, postulate, hole, permissive option, or termination
--     bypass.

import CastImprecisionShape as CastShape
open import Coercions using (Coercion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (_<_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Induction.WellFounded using (Acc)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
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
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveSynchronizationDef
  using (QuotientDownMode; quotient-down-mode)


WorldCoherentRightOneStepQuotientDownValueAccᵀ : Set₁
WorldCoherentRightOneStepQuotientDownValueAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ L′ : Term} {C C′ D D′ A A′ : Ty}
    {d d′ u u′ : Coercion} {d-shape d′-shape u-shape u′-shape}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (down-mode : QuotientDownMode) →
  (vV : Value V) →
  No• V →
  (vV′ : Value V′) →
  No• V′ →
  Acc _<_ (pendingAdministrationRank vV′ (d′ ∷ u′ ∷ [])) →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((V ⟨ d ⟩) ⟨ u ⟩) →
  RuntimeOK ((V′ ⟨ d′ ⟩) ⟨ u′ ⟩) →
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
  V′ ⟨ d′ ⟩ —→ L′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (V ⟨ d ⟩) ⟨ u ⟩}
    {N′ = L′ ⟨ u′ ⟩} {χ = keep} {ρ = ρ} pA
