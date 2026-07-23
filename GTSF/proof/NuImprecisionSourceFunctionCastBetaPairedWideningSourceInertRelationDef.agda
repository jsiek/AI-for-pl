module
  proof.NuImprecisionSourceFunctionCastBetaPairedWideningSourceInertRelationDef
  where

-- File Charter:
--   * Defines the pure term-imprecision obligation for beta-distributing two
--     paired function widenings in the source-inert compatibility case.
--   * Excludes world, reduction, value, runtime, and store-prefix bookkeeping.
--   * Contains no implementation, result/view carrier, postulate, hole, or
--     permissive option.

import Coercions as C
open import Coercions using (Inert)
open import Data.List using ([])

open import ImprecisionWf using
  (ImpCtx; _↦_; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (Term; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; _⇒_)


SourceFunctionCastBetaPairedWideningSourceInertRelationᵀ :
  Set₁
SourceFunctionCastBetaPairedWideningSourceInertRelationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W L′ R′ : Term} {c d e f : C.Coercion}
    {A₀ A₀′ A A′ B₀ B₀′ B B′ : Ty}
    {pA₀ : Φ ∣ Δᴸ ⊢ A₀ ⊑ A₀′ ⊣ Δᴿ}
    {pB₀ : Φ ∣ Δᴸ ⊢ B₀ ⊑ B₀′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {μ μ′} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ
    ⊢ c C.↦ d ∶ A₀ ⇒ B₀ ⊑ A ⇒ B →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ
    ⊢ e C.↦ f ∶ A₀′ ⇒ B₀′ ⊑ A′ ⇒ B′ →
  Inert (c C.↦ d) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ L′
      ⦂ A₀ ⇒ B₀ ⊑ A₀′ ⇒ B₀′ ∶ pA₀ ↦ pB₀ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ (V · (W ⟨ c ⟩)) ⟨ d ⟩
      ⊑ (L′ · (R′ ⟨ e ⟩)) ⟨ f ⟩
      ⦂ B ⊑ B′ ∶ pB
