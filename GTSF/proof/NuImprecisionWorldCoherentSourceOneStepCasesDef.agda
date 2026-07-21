module proof.NuImprecisionWorldCoherentSourceOneStepCasesDef where

-- File Charter:
--   * Defines the nine source-reduction case capabilities used by the exact
--     source one-step dispatcher.
--   * Keeps every ambient-prefix, typing, runtime, store, and world premise
--     explicit at each major reduction-family boundary.
--   * Contains no dispatcher, case implementation, postulate, or hole.

open import Data.List using ([])

open import Coercions using (Coercion)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  ( Shiftable
  ; StoreChange
  ; applyCoercion
  ; applyCoercionUnderTyBinder
  ; applyTerm
  ; applyTy
  ; bind
  ; keep
  ; _—→_
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; blame
  ; ν
  ; ⇑ᵗᵐ
  ; _·_
  ; _•
  ; _⟨_⟩
  ; _⊕[_]_
  )
open import Primitives using (Prim)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)
open import proof.NuImprecisionWorldCoherentSourcePureStepCasesDef using
  (WorldCoherentSourcePureStepCases)
open import TermTyping using (_∣_∣_⊢_⦂_)


record WorldCoherentSourceOneStepCases : Set₁ where
  field
    sourcePureStepCases : WorldCoherentSourcePureStepCases

    sourceAllocationStepCase :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {C : Ty} {V M′ : Term} {c : Coercion} {A B : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (ν C V c) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ ν C V c ⦂ A →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ ν C V c ⊑ M′ ⦂ A ⊑ B ∶ p →
      Value V →
      No• V →
      WorldCoherentSourceOneStepIndexedResult
        {M = ν C V c} {M′ = M′}
        {L = ((⇑ᵗᵐ V) •) ⟨ c ⟩}
        {χ = bind C} {ρ = ρ⁺} p

    sourceApplicationLeftStepCase :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {χ : StoreChange} {L M L′ M′ : Term} {A B : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (L · M) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ L · M ⦂ A →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ L · M ⊑ M′ ⦂ A ⊑ B ∶ p →
      L —→[ χ ] L′ →
      Shiftable χ M →
      WorldCoherentSourceOneStepIndexedResult
        {M = L · M} {M′ = M′}
        {L = L′ · applyTerm χ M} {χ = χ} {ρ = ρ⁺} p

    sourceApplicationRightStepCase :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {χ : StoreChange} {V M M₁ M′ : Term} {A B : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (V · M) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ V · M ⦂ A →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V · M ⊑ M′ ⦂ A ⊑ B ∶ p →
      Value V →
      Shiftable χ V →
      M —→[ χ ] M₁ →
      WorldCoherentSourceOneStepIndexedResult
        {M = V · M} {M′ = M′}
        {L = applyTerm χ V · M₁} {χ = χ} {ρ = ρ⁺} p

    sourceCastFrameStepCase :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {χ : StoreChange} {M M₁ M′ : Term} {c : Coercion}
        {A B : Ty} {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (M ⟨ c ⟩) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ M ⟨ c ⟩ ⦂ A →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⟨ c ⟩ ⊑ M′ ⦂ A ⊑ B ∶ p →
      M —→[ χ ] M₁ →
      WorldCoherentSourceOneStepIndexedResult
        {M = M ⟨ c ⟩} {M′ = M′}
        {L = M₁ ⟨ applyCoercion χ c ⟩}
        {χ = χ} {ρ = ρ⁺} p

    sourceNuFrameStepCase :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {χ : StoreChange} {C : Ty} {L L′ M′ : Term}
        {c : Coercion} {A B : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (ν C L c) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ ν C L c ⦂ A →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ ν C L c ⊑ M′ ⦂ A ⊑ B ∶ p →
      L —→[ χ ] L′ →
      WorldCoherentSourceOneStepIndexedResult
        {M = ν C L c} {M′ = M′}
        {L = ν (applyTy χ C) L′
          (applyCoercionUnderTyBinder χ c)}
        {χ = χ} {ρ = ρ⁺} p

    sourceNuBlameStepCase :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {C : Ty} {c : Coercion} {M′ : Term} {A B : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (ν C blame c) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ ν C blame c ⦂ A →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ ν C blame c ⊑ M′ ⦂ A ⊑ B ∶ p →
      WorldCoherentSourceOneStepIndexedResult
        {M = ν C blame c} {M′ = M′} {L = blame}
        {χ = keep} {ρ = ρ⁺} p

    sourcePrimitiveLeftStepCase :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {χ : StoreChange} {L M L′ M′ : Term} {op : Prim}
        {A B : Ty} {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (L ⊕[ op ] M) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ L ⊕[ op ] M ⦂ A →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ L ⊕[ op ] M ⊑ M′ ⦂ A ⊑ B ∶ p →
      L —→[ χ ] L′ →
      Shiftable χ M →
      WorldCoherentSourceOneStepIndexedResult
        {M = L ⊕[ op ] M} {M′ = M′}
        {L = L′ ⊕[ op ] applyTerm χ M}
        {χ = χ} {ρ = ρ⁺} p

    sourcePrimitiveRightStepCase :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {χ : StoreChange} {L M M₁ M′ : Term} {op : Prim}
        {A B : Ty} {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (L ⊕[ op ] M) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ L ⊕[ op ] M ⦂ A →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ B →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ L ⊕[ op ] M ⊑ M′ ⦂ A ⊑ B ∶ p →
      Value L →
      Shiftable χ L →
      M —→[ χ ] M₁ →
      WorldCoherentSourceOneStepIndexedResult
        {M = L ⊕[ op ] M} {M′ = M′}
        {L = applyTerm χ L ⊕[ op ] M₁}
        {χ = χ} {ρ = ρ⁺} p

open WorldCoherentSourceOneStepCases public
