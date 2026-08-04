module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepAtomicAndBlameRootsDef
  where

-- File Charter:
--   * Defines target-oriented world-coherent leaves for atomic identity and
--     target blame roots.
--   * Atomic identity preserves the current world; target blame produces a
--     source trace to blame and therefore needs no successor-world witness.
--   * Contains no implementation, recursion, postulate, hole, or permissive
--     option.

open import Data.List using ([])
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using (keep)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; Value
  ; blame
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( Atom
  ; Ty
  ; TyCtx
  )
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


record WorldCoherentRightOneStepAtomicAndBlameRoots : Set₁ where
  field
    rightStepSourceBlameRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {N′ : Term} {A B : Ty} {χ}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = blame} {N′ = N′} {χ = χ} {ρ = ρ} p

    rightStepTargetAtomicIdentityRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M V : Term} {A B : Ty}
        {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      Atom B →
      Value V →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ V ⦂ A ⊑ B ∶ p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = V} {χ = keep} {ρ = ρ} q

    rightStepTargetBlameRoot :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {M : Term} {A B C : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
      RuntimeOK M →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
        ⊢ᴺ M ⊑ blame ⦂ A ⊑ B ∶ p →
      WorldCoherentWeakOneStepIndexedOutcome
        {M = M} {N′ = blame} {χ = keep} {ρ = ρ} q

open WorldCoherentRightOneStepAtomicAndBlameRoots public
