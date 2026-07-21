module
  proof.NuImprecisionWorldCoherentSourceAllocationPairedIndexStepsDef
  where

-- File Charter:
--   * Defines the two exact source-allocation leaves whose inner universal
--     precision index is paired `∀ⁱ` rather than source-only `ν`.
--   * Keeps the distinguished allocation step exact for ordinary `ν` and
--     `ν ★`; later source catch-up is deliberately outside this boundary.
--   * Both fields return the existing complete source-step result directly,
--     with no paired-index result or outcome carrier.
--   * Contains no implementation, dispatcher, postulate, hole, or option.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)

open import Coercions using (Coercion; ModeEnv; instᵈ)
open import Conversion using (RevealConversion)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_)
open import NuReduction using (bind)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( CtxImpEntry
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; ν
  ; ⇑ᵗᵐ
  ; _•
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  (Ty; TyCtx; WfTy; ★; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.NuImprecisionWorldCoherentSourceOneStepResultDef
  using (WorldCoherentSourceOneStepIndexedResult)


record WorldCoherentSourceAllocationPairedIndexSteps : Set₁ where
  field
    sourceAllocationNuPairedIndexStep :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρᴸ : StoreImp
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {A B C C′ : Ty} {V M′ : Term} {s : Coercion}
        {μ : ModeEnv}
        {p : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
        {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (ν A V s) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ ν A V s ⦂ B →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ `∀ C′ →
      WfTy Δᴸ A →
      (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
      RevealConversion μ (suc Δᴸ)
        ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
        zero (⇑ᵗ A) s C (⇑ᵗ B) →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
        ([] {A = CtxImpEntry
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ r →
      Value V →
      No• V →
      WorldCoherentSourceOneStepIndexedResult
        {M = ν A V s} {M′ = M′}
        {L = ((⇑ᵗᵐ V) •) ⟨ s ⟩}
        {χ = bind A} {ρ = ρ⁺} p

    sourceAllocationNuCastPairedIndexStep :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρᴸ : StoreImp
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {B C C′ : Ty} {V M′ : Term} {s : Coercion}
        {μ : ModeEnv}
        {p : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
        {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
          ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      StoreWf Δᴸ (leftStoreⁱ ρ⁺) →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK (ν ★ V s) →
      RuntimeOK M′ →
      Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ [] ⊢ ν ★ V s ⦂ B →
      Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ [] ⊢ M′ ⦂ `∀ C′ →
      CastMode μ →
      SealModeStore★ (instᵈ μ)
        ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)) →
      instᵈ μ ∣ suc Δᴸ
        ∣ ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
        ⊢ s ∶ C ⊑ ⇑ᵗ B →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
      LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
        ([] {A = CtxImpEntry
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ V ⊑ M′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ r →
      Value V →
      No• V →
      WorldCoherentSourceOneStepIndexedResult
        {M = ν ★ V s} {M′ = M′}
        {L = ((⇑ᵗᵐ V) •) ⟨ s ⟩}
        {χ = bind ★} {ρ = ρ⁺} p

open WorldCoherentSourceAllocationPairedIndexSteps public
