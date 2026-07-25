module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaDef
  where

-- File Charter:
--   * Defines target function-cast beta scheduling before and after source
--     application operands have been caught up to values.
--   * Keeps the target post-beta application and result cast explicit.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility wrapper.

import Coercions as C
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
  ( RuntimeOK
  ; Term
  ; Value
  ; ƛ_
  ; _·_
  ; _⟨_⟩
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


WorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesᵀ : Set₁
WorldCoherentRightOneStepApplicationFunctionCastBetaLambdaValuesᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {N M V′ W′ : Term} {e f : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK ((ƛ N) · M) →
  RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ ƛ N ⊑ V′ ⟨ e C.↦ f ⟩
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ W′ ⦂ A ⊑ A′ ∶ pA →
  Value M →
  Value V′ →
  Value W′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (ƛ N) · M}
    {N′ = (V′ · (W′ ⟨ e ⟩)) ⟨ f ⟩}
    {χ = keep} {ρ = ρ} pB


WorldCoherentRightOneStepApplicationFunctionCastBetaValuesᵀ : Set₁
WorldCoherentRightOneStepApplicationFunctionCastBetaValuesᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L M V′ W′ : Term} {e f : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK (L · M) →
  RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ V′ ⟨ e C.↦ f ⟩
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ W′ ⦂ A ⊑ A′ ∶ pA →
  Value L →
  Value M →
  Value V′ →
  Value W′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L · M}
    {N′ = (V′ · (W′ ⟨ e ⟩)) ⟨ f ⟩}
    {χ = keep} {ρ = ρ} pB


WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueᵀ :
  Set₁
WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L M V′ W′ : Term} {e f : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK (L · M) →
  RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ V′ ⟨ e C.↦ f ⟩
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ W′ ⦂ A ⊑ A′ ∶ pA →
  Value L →
  Value V′ →
  Value W′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L · M}
    {N′ = (V′ · (W′ ⟨ e ⟩)) ⟨ f ⟩}
    {χ = keep} {ρ = ρ} pB


WorldCoherentRightOneStepApplicationFunctionCastBetaᵀ : Set₁
WorldCoherentRightOneStepApplicationFunctionCastBetaᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L M V′ W′ : Term} {e f : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK (L · M) →
  RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ V′ ⟨ e C.↦ f ⟩
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ W′ ⦂ A ⊑ A′ ∶ pA →
  Value V′ →
  Value W′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L · M}
    {N′ = (V′ · (W′ ⟨ e ⟩)) ⟨ f ⟩}
    {χ = keep} {ρ = ρ} pB
