module
  proof.WorldCoherent.Right.Core.NuImprecisionWorldCoherentRightQuotientDownUpFrameDef
  where

-- File Charter:
--   * Defines the exact world-coherent right frame for one live
--     `closeᵀ (paired-downᵀ ...)` boundary.
--   * Retains both spine modes, all narrowing and widening shapes and
--     composition squares, and both reduction-closed compatibility witnesses.
--   * Contains no implementation, dispatcher, stale id/gen split, fragment
--     alias, compatibility wrapper, postulate, hole, or permissive option.

open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing; widening)
open import Coercions using
  (Coercion; Inert)
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; _；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientImprecisionCompatibility using
  ( QuotientNarrowingEliminationCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; SpineCastMode
  )
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using
  (Ty; TyCtx)
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
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using (WorldCoherentRightValueCatchupIndexedResult)


record WorldCoherentRightQuotientDownUpFrame : Set₁ where
  field
    rightQuotientDownUpFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {C C′ D D′ A A′ : Ty}
        {d d′ u u′ : Coercion} {μ μ′}
        {d-shape d′-shape u-shape u′-shape : ImprecisionShape}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK ((M′ ⟨ d′ ⟩) ⟨ u′ ⟩) →
      Value M →
      No• M →
      Inert d →
      Inert u →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ pC →
      SpineCastMode (leftStoreⁱ ρ₀) μ →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ d ∶ C ⊒ D →
      narrowing ⊢ᶜ d ⦂ d-shape →
      SpineCastMode (rightStoreⁱ ρ₀) μ′ →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ d′ ∶ C′ ⊒ D′ →
      narrowing ⊢ᶜ d′ ⦂ d′-shape →
      d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
      QuotientNarrowingEliminationCompatible
        Φ Δᴸ Δᴿ d d′ pC qD d-shape d′-shape →
      QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
      widening ⊢ᶜ u ⦂ u-shape →
      widening ⊢ᶜ u′ ⦂ u′-shape →
      u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
      ReductionClosedQuotientWideningCompatible
        Φ Δᴸ Δᴿ u u′ qD pA u-shape u′-shape →
      WorldCoherentRightValueCatchupIndexedResult
        {V = M} {M′ = M′} {ρ = ρ⁺} pC →
      WorldCoherentRightValueCatchupIndexedResult
        {V = (M ⟨ d ⟩) ⟨ u ⟩}
        {M′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩} {ρ = ρ⁺} pA

open WorldCoherentRightQuotientDownUpFrame public
