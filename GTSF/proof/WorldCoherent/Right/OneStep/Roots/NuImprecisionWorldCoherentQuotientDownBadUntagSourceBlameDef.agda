module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentQuotientDownBadUntagSourceBlameDef
  where

-- File Charter:
--   * Defines source-blame synchronization for a failed target tag/untag root
--     at one live paired narrowing boundary.
--   * Retains exactly the coherent source and target values, paired downcast
--     typing, quotient square, and narrowing-elimination compatibility needed
--     before any closing widening is applied.
--   * Returns the source-downcast-to-blame trace reused by every enclosing
--     source evaluation context.
--   * Contains no implementation, closing-widening premise, result wrapper,
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
open import NuReduction using (_—→_; _—↠[_]_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; blame; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import QuotientImprecisionCompatibility using
  (QuotientNarrowingEliminationCompatible)
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


WorldCoherentQuotientDownBadUntagSourceBlameᵀ : Set₁
WorldCoherentQuotientDownBadUntagSourceBlameᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {C C′ D D′ G H : Ty}
    {d : Coercion} {d-shape d′-shape}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
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
  RuntimeOK (V ⟨ d ⟩) →
  RuntimeOK ((W ⟨ G ! ⟩) ⟨ H ？ ⟩) →
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
  (W ⟨ G ! ⟩) ⟨ H ？ ⟩ —→ blame →
  ∃[ χs ] ((V ⟨ d ⟩) —↠[ χs ] blame)
