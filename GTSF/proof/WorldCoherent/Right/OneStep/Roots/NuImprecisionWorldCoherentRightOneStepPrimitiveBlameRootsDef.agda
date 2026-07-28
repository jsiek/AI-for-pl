module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPrimitiveBlameRootsDef
  where

-- File Charter:
--   * Defines the two target primitive-blame roots for world-coherent
--     target-oriented one-step simulation.
--   * The left root catches up a source operand related to blame; the right
--     root first catches up a source operand related to a target value.
--   * Both roots finish with source blame and therefore expose no continuing
--     successor-world branch.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, delta root, or compatibility wrapper.

open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; idι
  )
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; blame
  ; _⊕[_]_
  )
open import Primitives using (addℕ)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( TyCtx
  ; `ℕ
  ; ‵_
  )
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


record WorldCoherentRightOneStepPrimitiveBlameRoots : Set₁ where
  field
    rightStepTargetPrimitiveLeftBlameRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {L M : Term} →
      RuntimeOK (L ⊕[ addℕ ] M) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ L ⊑ blame ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = L ⊕[ addℕ ] M} {N′ = blame}
        {A = ‵ `ℕ} {B = ‵ `ℕ}
        {χ = keep} {ρ = ρ} idι

    rightStepTargetPrimitiveRightBlameRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {L M V′ : Term} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      RuntimeOK (L ⊕[ addℕ ] M) →
      Value V′ →
      No• V′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ L ⊑ V′ ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ blame ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = L ⊕[ addℕ ] M} {N′ = blame}
        {A = ‵ `ℕ} {B = ‵ `ℕ}
        {χ = keep} {ρ = ρ} idι

open WorldCoherentRightOneStepPrimitiveBlameRoots public
