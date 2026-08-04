module
  proof.Right.SourceAll.Frames.NuImprecisionRightSourceAllSourceFramesDef
  where

-- File Charter:
--   * Defines the four source-cast structural cases beneath a
--     source-universal right-value closing boundary.
--   * Requires `NonVar` and occurrence only for the actual outer body type;
--     any corresponding facts for the pre-cast type must be derived.
--   * Returns the existing complete catch-up carrier and introduces no
--     result, view, outcome, or frame-plan hierarchy.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using (narrowing; widening; _⊢ᶜ_⦂_)
open import Coercions using (Coercion; Inert)
open import Conversion using (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴸ_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Imprecision using (NonVar)
open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _∣_⊢_⊑_⊣_; ⇑ᴸᵢ; ν)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( LiftLeftCtxⁱ
  )
open import NuTerms using
  (No•; RuntimeOK; Term; Value; Λ_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; TyVar; occurs)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  (WorldCoherentRightValueCatchupIndexedResult)


record WorldCoherentRightSourceAllSourceFrames : Set₁ where
  field
    sourceAllSourceNarrowFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρᴸ : StoreImp
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {M N′ : Term} {A B B′ : Ty} {c : Coercion} {μ}
        {{safe : NonVar B}}
        {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {shape : ImprecisionShape}
        {occ : occurs zero B ≡ true} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK N′ →
      Value M →
      No• M →
      Inert c →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρᴸ) →
      μ ∣ suc Δᴸ ∣ leftStoreⁱ ρᴸ ⊢ c ∶ A ⊒ B →
      narrowing ⊢ᶜ c ⦂ shape →
      shape ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
      LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] [] →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ []
        ⊢ᴺ M ⊑ N′ ⦂ A ⊑ B′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = Λ (M ⟨ c ⟩)} {M′ = N′} {ρ = ρ⁺}
        (ν safe occ q)

    sourceAllSourceWidenFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρᴸ : StoreImp
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {M N′ : Term} {A B B′ : Ty} {c : Coercion} {μ}
        {{safe : NonVar B}}
        {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {shape : ImprecisionShape}
        {occ : occurs zero B ≡ true} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK N′ →
      Value M →
      No• M →
      Inert c →
      CastMode μ →
      SealModeStore★ μ (leftStoreⁱ ρᴸ) →
      μ ∣ suc Δᴸ ∣ leftStoreⁱ ρᴸ ⊢ c ∶ A ⊑ B →
      widening ⊢ᶜ c ⦂ shape →
      shape ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
      LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] [] →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ []
        ⊢ᴺ M ⊑ N′ ⦂ A ⊑ B′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = Λ (M ⟨ c ⟩)} {M′ = N′} {ρ = ρ⁺}
        (ν safe occ q)

    sourceAllSourceRevealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρᴸ : StoreImp
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {M N′ : Term} {A B B′ : Ty} {c : Coercion}
        {μ} {α : TyVar} {X : Ty}
        {{safe : NonVar B}}
        {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {occ : occurs zero B ≡ true} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK N′ →
      Value M →
      No• M →
      Inert c →
      RevealConversion μ (suc Δᴸ) (leftStoreⁱ ρᴸ)
        α X c A B →
      p [ α ↦ X ]ᴸ q →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
      LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] [] →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ []
        ⊢ᴺ M ⊑ N′ ⦂ A ⊑ B′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = Λ (M ⟨ c ⟩)} {M′ = N′} {ρ = ρ⁺}
        (ν safe occ q)

    sourceAllSourceConcealFrame :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {ρᴸ : StoreImp
          ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
        {M N′ : Term} {A B B′ : Ty} {c : Coercion}
        {μ} {α : TyVar} {X : Ty}
        {{safe : NonVar B}}
        {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
        {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
          ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
        {occ : occurs zero B ≡ true} →
      StoreImpPrefix ρ₀ ρ⁺ →
      WorldCoherent ρ⁺ →
      SourceNameExclusive Φ →
      AssumptionMembershipUnique Φ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      RuntimeOK N′ →
      Value M →
      No• M →
      Inert c →
      ConcealConversion μ (suc Δᴸ) (leftStoreⁱ ρᴸ)
        α X c A B →
      q [ α ↦ X ]ᴸ p →
      LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
      LiftLeftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) [] [] →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ []
        ⊢ᴺ M ⊑ N′ ⦂ A ⊑ B′ ∶ p →
      WorldCoherentRightValueCatchupIndexedResult
        {V = Λ (M ⟨ c ⟩)} {M′ = N′} {ρ = ρ⁺}
        (ν safe occ q)

open WorldCoherentRightSourceAllSourceFrames public
