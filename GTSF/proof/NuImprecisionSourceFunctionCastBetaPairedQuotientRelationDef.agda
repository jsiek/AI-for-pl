module
  proof.NuImprecisionSourceFunctionCastBetaPairedQuotientRelationDef
  where

-- File Charter:
--   * Defines the pure term-imprecision obligation for beta-distributing a
--     quotient-related pair of function casts.
--   * Excludes world, reduction, value, runtime, and store-prefix bookkeeping.
--   * Contains no implementation, result/view carrier, postulate, hole, or
--     permissive option.

import Coercions as C
open import Data.List using ([])

open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using
  (Term; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty; TyCtx; _⇒_)


SourceFunctionCastBetaPairedQuotientRelationᵀ : Set₁
SourceFunctionCastBetaPairedQuotientRelationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W L′ R′ : Term} {c d e f : C.Coercion}
    {D D′ A A′ B B′ : Ty}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺᵖ V ⊑ L′ ⦂ D ⊑ᵖ D′ ∶ qD →
  QuotientWideningPair Δᴸ Δᴿ ρ
    (c C.↦ d) (e C.↦ f)
    D D′ (A ⇒ B) (A′ ⇒ B′) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ R′ ⦂ A ⊑ A′ ∶ pA →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ (V · (W ⟨ c ⟩)) ⟨ d ⟩
      ⊑ (L′ · (R′ ⟨ e ⟩)) ⟨ f ⟩
      ⦂ B ⊑ B′ ∶ pB
