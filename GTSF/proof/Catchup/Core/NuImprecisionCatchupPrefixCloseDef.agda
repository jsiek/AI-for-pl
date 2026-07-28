module proof.Catchup.Core.NuImprecisionCatchupPrefixCloseDef where

-- File Charter:
--   * Defines the mechanical left-silent closing contract for one live
--     `paired-downᵀ` quotient boundary and its compatible outer widening.
--   * Exposes the exact transported quotient relation as an input so semantic
--     terminal catch-up remains with the world-coherent caller.
--   * Contains no implementation, semantic dispatcher, postulate, hole, or
--     permissive option.

open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyTy; applyTys; keep)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import QuotientImprecisionCompatibility using
  (ReductionClosedQuotientWideningCompatible)
open import Types using (Ty; TyCtx)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftCatchupIndexedResult
  ; LeftSilentIndexedResult
  ; catchupIndexedResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceResult
  ; targetResult
  ; targetTailChanges
  ; weakIndexedResult
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using (weak-one-step-transport-quotientᵀ)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)


LeftSilentIndexedPrefixCloseᵀ : Set₁
LeftSilentIndexedPrefixCloseᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ D D′ A A′ : Ty}
    {d d′ u u′} {s s′}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  widening ⊢ᶜ u ⦂ s →
  widening ⊢ᶜ u′ ⦂ s′ →
  s ；⌊ pA ⌋≋ᵖ qD ； s′ →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u u′ qD pA s s′ →
  (catchup : LeftCatchupIndexedResult
    {N = M} {V′ = M′} {ρ = ρ⁺} pC) →
  let indexed = catchupIndexedResult catchup
      inner = weakIndexedResult indexed
  in
  AssumptionMembershipUnique (resultCtx inner) →
  (resultCtx inner
    ∣ resultLeftCtx inner
    ∣ resultRightCtx inner
    ∣ resultStore inner ∣ []
    ⊢ᴺᵖ (sourceResult inner ⟨
        applyCoercions (sourceChanges inner) d ⟩)
      ⊑ (targetResult inner ⟨ d′ ⟩)
    ⦂ applyTys (sourceChanges inner) D ⊑ᵖ
      applyTys (targetTailChanges inner) (applyTy keep D′)
    ∶ weak-one-step-transport-quotientᵀ inner qD) →
  LeftSilentIndexedResult
    {N = (M ⟨ d ⟩) ⟨ u ⟩}
    {V′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ⁺} pA
