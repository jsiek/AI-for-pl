module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRankedDef
  where

-- File Charter:
--   * Defines exact-rank variants of target ordinary-lambda beta scheduling
--     for a caught source function and for an arbitrary source argument.
--   * Indexes the source-function-cast cell by the rank of its inner source
--     function, making the recursive call structurally smaller.
--   * Keeps the rank private to the canonical SCC boundary and preserves the
--     public unranked contracts.
--   * Contains no implementation, recursion, result wrapper, postulate, hole,
--     permissive option, or compatibility alias.

import Coercions as C
open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import ImprecisionWf using
  ( ImpCtx
  ; _↦_
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
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
  proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureDef
  using (targetFunctionCastSpineRank)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (WorldCoherentWeakOneStepIndexedOutcome)


WorldCoherentRightOneStepApplicationLambdaBetaValuesAtᵀ : ℕ → Set₁
WorldCoherentRightOneStepApplicationLambdaBetaValuesAtᵀ n =
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
  (vL : Value L) →
  Value M →
  Value V′ →
  targetFunctionCastSpineRank vL ≡ n →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L · M} {N′ = N′ [ V′ ]}
    {χ = keep} {ρ = ρ} pB


WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueAtᵀ :
  ℕ → Set₁
WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueAtᵀ n =
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
  (vL : Value L) →
  Value V′ →
  targetFunctionCastSpineRank vL ≡ n →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = L · M} {N′ = N′ [ V′ ]}
    {χ = keep} {ρ = ρ} pB


WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesAtᵀ :
  ℕ → Set₁
WorldCoherentRightOneStepApplicationLambdaBetaFunctionCastValuesAtᵀ n =
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
  (vV : Value V) →
  Value W →
  Value V′ →
  targetFunctionCastSpineRank vV ≡ n →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (V ⟨ c C.↦ d ⟩) · W} {N′ = N′ [ V′ ]}
    {χ = keep} {ρ = ρ} pB
