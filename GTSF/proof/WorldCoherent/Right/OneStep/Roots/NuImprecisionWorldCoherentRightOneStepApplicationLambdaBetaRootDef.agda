module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRootDef
  where

-- File Charter:
--   * Defines the target-oriented ordinary-lambda beta root after both
--     application operands have been caught up to values.
--   * Exposes the related lambda bodies and related arguments needed by
--     quotiented substitution.
--   * Returns the source beta step against the already-reduced target body.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility wrapper.

open import Data.List using ([]; _∷_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using (keep)
open import NuTermImprecision using
  ( StoreImp
  ; ctx-imp
  )
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; ƛ_
  ; _·_
  ; _[_]
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using
  ( Ty
  ; TyCtx
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


WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ : Set₁
WorldCoherentRightOneStepApplicationLambdaBetaRootᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {N N′ V V′ : Term} {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  No• N →
  No• N′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp A A′ pA ∷ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (ƛ N) · V} {N′ = N′ [ V′ ]}
    {χ = keep} {ρ = ρ} pB
