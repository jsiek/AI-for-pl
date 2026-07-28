module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaPairedDef
  where

-- File Charter:
--   * Defines the four paired source/target function-cast beta terminals:
--     live reveal, conceal, widening, and quotient closure.
--   * States exact constructor evidence directly; ordinary paired casts are
--     never hidden behind endpoint syntax or a retired carrier.
--   * Keeps quotient closure distinct from the three ordinary QTI cases.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, alias, or compatibility wrapper.

import CastImprecisionShape as CastShape
import Coercions as C
open import Conversion using
  (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using
  (_[_↦_⊑⟨_⟩_↤_]ᴾ_)
open import Data.List using ([])
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using
  ( ImprecisionShape
  ; ⌊_⌋
  ; _；_≋_
  ; _；⌊_⌋≋ᵖ_；_
  )
open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_)
open import NuReduction using (keep)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreCorresponds
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  (RuntimeOK; Term; Value; _·_; _⟨_⟩)
open import QuotientImprecisionCompatibility using
  ( ReductionClosedPairedWideningCompatible
  ; ReductionClosedQuotientWideningCompatible
  )
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; _⇒_)
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


record WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues :
    Set₁ where
  field
    rightStepApplicationFunctionCastBetaPairedRevealValues :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {V M V′ W′ : Term} {c d e f : C.Coercion}
        {C C′ A A′ B B′ X X′ : Ty}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {α β pX μ μ′} →
      StoreImpPrefix ρᵇ ρ →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      RuntimeOK ((V ⟨ c C.↦ d ⟩) · M) →
      RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
      StoreCorresponds ρᵇ α X β X′ pX →
      RevealConversion μ Δᴸ (leftStoreⁱ ρᵇ)
        α X (c C.↦ d) C (A ⇒ B) →
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρᵇ)
        β X′ (e C.↦ f) C′ (A′ ⇒ B′) →
      pC [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ (pA ↦ pB) →
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

    rightStepApplicationFunctionCastBetaPairedConcealValues :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {V M V′ W′ : Term} {c d e f : C.Coercion}
        {C C′ A A′ B B′ X X′ : Ty}
        {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {α β pX μ μ′} →
      StoreImpPrefix ρᵇ ρ →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      RuntimeOK ((V ⟨ c C.↦ d ⟩) · M) →
      RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
      StoreCorresponds ρᵇ α X β X′ pX →
      ConcealConversion μ Δᴸ (leftStoreⁱ ρᵇ)
        α X (c C.↦ d) C (A ⇒ B) →
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρᵇ)
        β X′ (e C.↦ f) C′ (A′ ⇒ B′) →
      (pA ↦ pB) [ α ↦ X ⊑⟨ pX ⟩ X′ ↤ β ]ᴾ pC →
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

    rightStepApplicationFunctionCastBetaPairedWideningValues :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρᵇ ρ : StoreImp Φ Δᴸ Δᴿ}
        {V M V′ W′ : Term} {c d e f : C.Coercion}
        {A₀ A₀′ A A′ B₀ B₀′ B B′ : Ty}
        {pA₀ : Φ ∣ Δᴸ ⊢ A₀ ⊑ A₀′ ⊣ Δᴿ}
        {pB₀ : Φ ∣ Δᴸ ⊢ B₀ ⊑ B₀′ ⊣ Δᴿ}
        {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
        {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {s s′ r : ImprecisionShape} {μ μ′} →
      StoreImpPrefix ρᵇ ρ →
      WorldCoherent ρ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ) →
      RuntimeOK ((V ⟨ c C.↦ d ⟩) · M) →
      RuntimeOK ((V′ ⟨ e C.↦ f ⟩) · W′) →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρᵇ) →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρᵇ
        ⊢ c C.↦ d ∶ A₀ ⇒ B₀ ⊑ A ⇒ B →
      CastShape.widening CastShape.⊢ᶜ
        c C.↦ d ⦂ s →
      CastMode μ′ →
      SealModeStore★ μ′ (rightStoreⁱ ρᵇ) →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρᵇ
        ⊢ e C.↦ f ∶ A₀′ ⇒ B₀′ ⊑ A′ ⇒ B′ →
      CastShape.widening CastShape.⊢ᶜ
        e C.↦ f ⦂ s′ →
      s ； ⌊ pA ↦ pB ⌋ ≋ r →
      ⌊ pA₀ ↦ pB₀ ⌋ ； s′ ≋ r →
      ReductionClosedPairedWideningCompatible Φ Δᴸ Δᴿ
        (c C.↦ d) (e C.↦ f)
        (pA₀ ↦ pB₀) (pA ↦ pB) s s′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρᵇ ∣ []
        ⊢ᴺ V ⊑ V′
          ⦂ A₀ ⇒ B₀ ⊑ A₀′ ⇒ B₀′ ∶ pA₀ ↦ pB₀ →
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

    rightStepApplicationFunctionCastBetaPairedQuotientValues :
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
      CastShape.widening CastShape.⊢ᶜ
        (c C.↦ d) ⦂ s →
      CastShape.widening CastShape.⊢ᶜ
        (e C.↦ f) ⦂ s′ →
      s ；⌊ pA ↦ pB ⌋≋ᵖ qD ； s′ →
      ReductionClosedQuotientWideningCompatible
        Φ Δᴸ Δᴿ (c C.↦ d) (e C.↦ f)
        qD (pA ↦ pB) s s′ →
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

open WorldCoherentRightOneStepApplicationFunctionCastBetaPairedValues public
