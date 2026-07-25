module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueDef
  where

-- File Charter:
--   * Defines target ordinary-lambda beta scheduling after the source
--     function has been caught up to a value.
--   * Separates the value/value terminal from the source-argument catch-up
--     stage so recursive function-cast scheduling can reuse the latter.
--   * Keeps the source store and every world invariant explicit.
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
  ; _[_]
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


WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesᵀ :
  Set₁
WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W N′ V′ : Term} {c d : C.Coercion}
    {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · W) →
  RuntimeOK ((ƛ N′) · V′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⟨ c C.↦ d ⟩ ⊑ ƛ N′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  Value W →
  Value V′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (V ⟨ c C.↦ d ⟩) · W} {N′ = N′ [ V′ ]}
    {χ = keep} {ρ = ρ} pB


WorldCoherentRightOneStepApplicationLambdaBetaValuesᵀ : Set₁
WorldCoherentRightOneStepApplicationLambdaBetaValuesᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L M N′ V′ : Term} {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK (L · M) →
  RuntimeOK ((ƛ N′) · V′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ ƛ N′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
  Value L →
  Value M →
  Value V′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L · M} {N′ = N′ [ V′ ]}
    {χ = keep} {ρ = ρ} pB


WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueᵀ :
  Set₁
WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L M N′ V′ : Term} {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK (L · M) →
  RuntimeOK ((ƛ N′) · V′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ ƛ N′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
  Value L →
  Value V′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L · M} {N′ = N′ [ V′ ]}
    {χ = keep} {ρ = ρ} pB


WorldCoherentRightOneStepApplicationLambdaBetaᵀ : Set₁
WorldCoherentRightOneStepApplicationLambdaBetaᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L M N′ V′ : Term} {A A′ B B′ : Ty}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK (L · M) →
  RuntimeOK ((ƛ N′) · V′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ ƛ N′
      ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V′ ⦂ A ⊑ A′ ∶ pA →
  Value V′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L · M} {N′ = N′ [ V′ ]}
    {χ = keep} {ρ = ρ} pB
