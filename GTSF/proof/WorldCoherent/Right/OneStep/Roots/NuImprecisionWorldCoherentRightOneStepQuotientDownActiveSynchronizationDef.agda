module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveSynchronizationDef
  where

-- File Charter:
--   * Defines the exact active target-down synchronization shared by the
--     `down⊑downᵀ` and `gen-down⊑gen-downᵀ` QTIP constructors.
--   * Restricts the downcast mode to the two modes admitted by those
--     constructors and retains both composition squares and the enclosing
--     quotient-widening pair.
--   * Contains no frame recursion, application case, implementation,
--     dispatcher, postulate, hole, permissive option, or wrapper alias.

import CastImprecisionShape as CastShape
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; genᵈ
  ; id-onlyᵈ
  ; tag-or-idᵈ
  )
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using (keep; _—→_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
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


data QuotientDownMode : Set where
  id-down : QuotientDownMode
  gen-down : QuotientDownMode


quotient-down-mode : QuotientDownMode → ModeEnv
quotient-down-mode id-down = id-onlyᵈ
quotient-down-mode gen-down = genᵈ tag-or-idᵈ


WorldCoherentRightOneStepQuotientDownActiveSynchronizationᵀ : Set₁
WorldCoherentRightOneStepQuotientDownActiveSynchronizationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {M V′ L′ : Term} {C C′ D D′ A A′ : Ty}
    {d d′ u u′ : Coercion} {d-shape d′-shape u-shape u′-shape}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (down-mode : QuotientDownMode) →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreImpPrefix ρᵇ ρ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
  RuntimeOK ((V′ ⟨ d′ ⟩) ⟨ u′ ⟩) →
  Value V′ →
  quotient-down-mode down-mode ∣ Δᴸ ∣ leftStoreⁱ ρᵇ
    ⊢ d ∶ C ⊒ D →
  CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
  quotient-down-mode down-mode ∣ Δᴿ ∣ rightStoreⁱ ρᵇ
    ⊢ d′ ∶ C′ ⊒ D′ →
  CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ d′-shape →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ M ⊑ V′ ⦂ C ⊑ C′ ∶ pC →
  d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ u u′ D D′ A A′ →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
  u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
  V′ ⟨ d′ ⟩ —→ L′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (M ⟨ d ⟩) ⟨ u ⟩}
    {N′ = L′ ⟨ u′ ⟩} {χ = keep} {ρ = ρ} pA
