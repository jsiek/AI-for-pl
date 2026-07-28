module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownBadUntagRootDef
  where

-- File Charter:
--   * Defines the terminal semantic leaf for a failed target tag/untag root
--     below one live `closeᵀ (paired-downᵀ ...)` boundary.
--   * Retains the exact coherent value world, original source down/up state,
--     both composition squares, and both compatibility witnesses.
--   * Returns the source-to-blame trace required by every weak outcome after
--     the failed target root.
--   * Contains no implementation, recursive worker, result wrapper,
--     postulate, hole, permissive option, compatibility alias, or
--     termination bypass.

import CastImprecisionShape as CastShape
open import Coercions using (Coercion; _!; _？)
open import Data.List using ([])
open import Data.Product using (∃-syntax)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  (StoreChanges; _—→_; _—↠[_]_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; blame; _⟨_⟩)
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
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveSynchronizationDef
  using (QuotientDownMode; quotient-down-mode)


WorldCoherentRightOneStepQuotientDownBadUntagRootᵀ : Set₁
WorldCoherentRightOneStepQuotientDownBadUntagRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {C C′ D D′ A A′ G H : Ty}
    {d u u′ : Coercion} {d-shape d′-shape u-shape u′-shape}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  (down-mode : QuotientDownMode) →
  (vV : Value V) →
  No• V →
  (vW : Value W) →
  No• W →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((V ⟨ d ⟩) ⟨ u ⟩) →
  RuntimeOK (((W ⟨ G ! ⟩) ⟨ H ？ ⟩) ⟨ u′ ⟩) →
  quotient-down-mode down-mode ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ d ∶ C ⊒ D →
  CastShape.narrowing CastShape.⊢ᶜ d ⦂ d-shape →
  quotient-down-mode down-mode ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ H ？ ∶ C′ ⊒ D′ →
  CastShape.narrowing CastShape.⊢ᶜ H ？ ⦂ d′-shape →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⟨ G ! ⟩ ⦂ C ⊑ C′ ∶ pC →
  d-shape ；⌊ pC ⌋≋ᵖ qD ； d′-shape →
  QuotientNarrowingEliminationCompatible
    Φ Δᴸ Δᴿ d (H ？) pC qD d-shape d′-shape →
  QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
  CastShape.widening CastShape.⊢ᶜ u ⦂ u-shape →
  CastShape.widening CastShape.⊢ᶜ u′ ⦂ u′-shape →
  u-shape ；⌊ pA ⌋≋ᵖ qD ； u′-shape →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u u′ qD pA u-shape u′-shape →
  (W ⟨ G ! ⟩) ⟨ H ？ ⟩ —→ blame →
  ∃[ χs ]
    (((V ⟨ d ⟩) ⟨ u ⟩) —↠[ χs ] blame)
