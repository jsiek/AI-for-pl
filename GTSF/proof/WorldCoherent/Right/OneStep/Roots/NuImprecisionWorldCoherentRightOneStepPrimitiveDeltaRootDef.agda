module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPrimitiveDeltaRootDef
  where

-- File Charter:
--   * Defines the target natural-addition delta root for world-coherent
--     target-oriented one-step simulation.
--   * Retains both exact operand relations while requiring the source
--     primitive term to satisfy the runtime-bullet invariant.
--   * Exposes every world invariant needed to catch both source operands up
--     before the matching source delta step.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, blame root, or compatibility wrapper.

open import Data.List using ([])
open import Data.Nat using (ℕ; _+_)
open import ImprecisionWf using
  ( ImpCtx
  ; idι
  )
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using
  ( RuntimeOK
  ; Term
  ; $
  ; _⊕[_]_
  )
open import Primitives using
  ( addℕ
  ; κℕ
  )
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


WorldCoherentRightOneStepPrimitiveDeltaRootᵀ : Set₁
WorldCoherentRightOneStepPrimitiveDeltaRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L M : Term} {m n : ℕ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK (L ⊕[ addℕ ] M) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ $ (κℕ m) ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ $ (κℕ n) ⦂ ‵ `ℕ ⊑ ‵ `ℕ ∶ idι →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L ⊕[ addℕ ] M} {N′ = $ (κℕ (m + n))}
    {A = ‵ `ℕ} {B = ‵ `ℕ}
    {χ = keep} {ρ = ρ} idι
