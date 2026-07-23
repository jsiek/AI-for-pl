module
  proof.WorldCoherent.Source.Misc.NuImprecisionWorldCoherentSourceSynchronizedLambdaBetaDef
  where

-- File Charter:
--   * States the synchronized ordinary-lambda beta root at one coherent world.
--   * Takes the related body and argument directly, after target scheduling has
--     exposed a target lambda and target value.
--   * Returns the canonical exact source one-step result without a new carrier.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using ([]; _∷_)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuTermImprecision using (StoreImp; ctx-imp)
open import NuTerms using (No•; Term; Value; ƛ_; _·_; _[_])
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceSynchronizedLambdaBetaᵀ : Set₁
WorldCoherentSourceSynchronizedLambdaBetaᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {N N′ V V′ : Term} {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  Value V → No• V →
  Value V′ → No• V′ →
  No• N → No• N′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ ctx-imp A A′ pA ∷ []
    ⊢ᴺ N ⊑ N′ ⦂ B ⊑ B′ ∶ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
  WorldCoherentSourceOneStepIndexedResult
    {M = (ƛ N) · V} {M′ = (ƛ N′) · V′}
    {L = N [ V ]} {χ = keep} {ρ = ρ} pB
