module proof.Store.Prefix.NuImprecisionTermStorePrefixDef where

-- File Charter:
--   * States admissible relational-store prefix weakening for the live
--     ordinary and quotient term-imprecision judgments.
--   * Keeps endpoint terms, types, contexts, and imprecision indices fixed.
--   * Requires endpoint typing in the enlarged world so runtime bullets and
--     target-instantiation residuals retain exact allocation lineage.
--   * Contains no implementation, postulate, hole, or permissive option.

open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  ; leftCtxⁱ
  ; rightCtxⁱ
  )
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx)


TermImprecisionStorePrefixᵀ : Set₁
TermImprecisionStorePrefixᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ leftCtxⁱ γ ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p


QuotientTermImprecisionStorePrefixᵀ : Set₁
QuotientTermImprecisionStorePrefixᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {D D′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
    ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
  Δᴸ ∣ leftStoreⁱ ρ⁺ ∣ leftCtxⁱ γ ⊢ M ⦂ D →
  Δᴿ ∣ rightStoreⁱ ρ⁺ ∣ rightCtxⁱ γ ⊢ M′ ⦂ D′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ γ
    ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q
