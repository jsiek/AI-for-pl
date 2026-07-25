module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedDef
  where

-- File Charter:
--   * Defines the two paired source/target function-cast beta terminals.
--   * Separates ordinary paired casts from quotient widening pairs while
--     retaining exact shapes, composition evidence, and store prefixes.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or compatibility wrapper.

import Coercions as C
import CastImprecisionShape as CastShape
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; _；⌊_⌋≋ᵖ_；_
  )
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
  ; _·_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( PairedCast
  ; QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
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


WorldCoherentRightOneStepApplicationFunctionCastBetaPairedCastValuesᵀ :
  Set₁
WorldCoherentRightOneStepApplicationFunctionCastBetaPairedCastValuesᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M V′ W′ : Term} {c d e f : C.Coercion}
    {A A′ B B′ C C′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · M) →
  RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
  PairedCast Φ Δᴸ Δᴿ ρᵇ
    (c C.↦ d) (e C.↦ f) pC (pA ↦ pB) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ C ⊑ C′ ∶ pC →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ W′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  Value M →
  Value V′ →
  Value W′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (V ⟨ c C.↦ d ⟩) · M}
    {N′ = (V′ · (W′ ⟨ e ⟩)) ⟨ f ⟩}
    {χ = keep} {ρ = ρ} pB


WorldCoherentRightOneStepApplicationFunctionCastBetaPairedQuotientValuesᵀ :
  Set₁
WorldCoherentRightOneStepApplicationFunctionCastBetaPairedQuotientValuesᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M V′ W′ : Term} {c d e f : C.Coercion}
    {D D′ A A′ B B′ : Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {s s′ : ImprecisionShape} →
  StoreImpPrefix ρᵇ ρ →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  RuntimeOK ((V ⟨ c C.↦ d ⟩) · M) →
  RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
    ⊢ᴺᵖ V ⊑ V′ ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρᵇ
    (c C.↦ d) (e C.↦ f)
    D D′ (A ⇒ B) (A′ ⇒ B′) →
  CastShape.widening CastShape.⊢ᶜ (c C.↦ d) ⦂ s →
  CastShape.widening CastShape.⊢ᶜ (e C.↦ f) ⦂ s′ →
  s ；⌊ pA ↦ pB ⌋≋ᵖ qD ； s′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ W′ ⦂ A ⊑ A′ ∶ pA →
  Value V →
  Value M →
  Value V′ →
  Value W′ →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = (V ⟨ c C.↦ d ⟩) · M}
    {N′ = (V′ · (W′ ⟨ e ⟩)) ⟨ f ⟩}
    {χ = keep} {ρ = ρ} pB


record WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues :
    Set₁ where
  field
    rightStepApplicationFunctionCastBetaPairedCastValues :
      WorldCoherentRightOneStepApplicationFunctionCastBetaPairedCastValuesᵀ

    rightStepApplicationFunctionCastBetaPairedQuotientValues :
      WorldCoherentRightOneStepApplicationFunctionCastBetaPairedQuotientValuesᵀ

open WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues public
