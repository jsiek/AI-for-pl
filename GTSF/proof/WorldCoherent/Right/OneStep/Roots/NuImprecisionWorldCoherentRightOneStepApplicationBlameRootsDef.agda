module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationBlameRootsDef
  where

-- File Charter:
--   * Defines the two target application-blame roots for world-coherent
--     target-oriented one-step simulation.
--   * The left root catches up a source function related to blame; the right
--     root first catches up a source function related to a target value.
--   * Both roots finish with source blame and therefore expose no continuing
--     successor-world branch.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility wrapper.

open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; blame
  ; _·_
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( Ty
  ; TyCtx
  ; _⇒_
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


record WorldCoherentRightOneStepApplicationBlameRoots : Set₁ where
  field
    rightStepTargetApplicationLeftBlameRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {L M : Term} {A A′ B B′ : Ty}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      RuntimeOK (L · M) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ L ⊑ blame
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = L · M} {N′ = blame} {χ = keep} {ρ = ρ} pB

    rightStepTargetApplicationRightBlameRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {L M V′ : Term} {A A′ B B′ : Ty}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      RuntimeOK (L · M) →
      Value V′ →
      No• V′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ L ⊑ V′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ blame ⦂ A ⊑ A′ ∶ pA →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = L · M} {N′ = blame} {χ = keep} {ρ = ρ} pB

open WorldCoherentRightOneStepApplicationBlameRoots public
