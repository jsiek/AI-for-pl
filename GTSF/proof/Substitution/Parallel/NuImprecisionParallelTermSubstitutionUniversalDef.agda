module proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionUniversalDef where

-- File Charter:
--   * States the paired and source-only `Λ` roots of framed, prefix-aware
--     parallel term substitution.
--   * Keeps the relation's inner store/context lifts and value facts explicit.
--   * Contains no implementation, result wrapper, postulate, hole, or
--     permissive option.

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)

open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _∣_⊢_⊑_⊣_
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᴸᵢ
  ; ⇑ᵢ
  ; ∀ⁱ_
  ; ν
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  ; LiftCtxⁱ
  ; LiftLeftCtxⁱ
  )
open import NuTerms using
  (No•; Substˣ; Term; Value; Λ_; substˣᵐ; ↑ᵗᵐ)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; `∀; occurs)
open import proof.Substitution.Term.NuImprecisionSubstitutionFrame using
  ( QuotientedSubstitutionEnvironmentFamily
  ; QuotientedSubstitutionFrame
  )


QuotientedParallelTermSubstitutionPairedUniversalᵀ : Set₁
QuotientedParallelTermSubstitutionPairedUniversalᵀ =
  ∀ {Φ₀ : ImpCtx} {Δ₀ᴸ Δ₀ᴿ : TyCtx}
    {ρ⁺₀ : StoreImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
    {γ₀ δ₀ : CtxImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
    {τ₀ τ₀′ : Substˣ} →
  (environment : QuotientedSubstitutionEnvironmentFamily
    ρ⁺₀ γ₀ δ₀ τ₀ τ₀′) →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₀↑ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {γ↑ : CtxImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {τ τ′ : Substˣ} {V V′ : Term} {A B : Ty}
    {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ suc Δᴿ} →
  QuotientedSubstitutionFrame ρ⁺₀ γ₀ δ₀ τ₀ τ₀′
    ρ⁺ γ δ τ τ′ →
  StoreImpPrefix ρ₀ ρ⁺ →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₀↑ →
  LiftCtxⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) γ γ↑ →
  Value V → Value V′ → No• V → No• V′ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ₀↑ ∣ γ↑
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ δ
    ⊢ᴺ Λ (substˣᵐ (↑ᵗᵐ τ) V)
      ⊑ Λ (substˣᵐ (↑ᵗᵐ τ′) V′)
      ⦂ `∀ A ⊑ `∀ B ∶ ∀ⁱ p


QuotientedParallelTermSubstitutionSourceUniversalᵀ : Set₁
QuotientedParallelTermSubstitutionSourceUniversalᵀ =
  ∀ {Φ₀ : ImpCtx} {Δ₀ᴸ Δ₀ᴿ : TyCtx}
    {ρ⁺₀ : StoreImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
    {γ₀ δ₀ : CtxImp Φ₀ Δ₀ᴸ Δ₀ᴿ}
    {τ₀ τ₀′ : Substˣ} →
  (environment : QuotientedSubstitutionEnvironmentFamily
    ρ⁺₀ γ₀ δ₀ τ₀ τ₀′) →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ₀↑ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ}
    {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {γ↑ : CtxImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ}
    {τ τ′ : Substˣ} {V N′ : Term} {A B : Ty}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {{safe : NonVar A}}
    {occ : occurs zero A ≡ true} →
  QuotientedSubstitutionFrame ρ⁺₀ γ₀ δ₀ τ₀ τ₀′
    ρ⁺ γ δ τ τ′ →
  StoreImpPrefix ρ₀ ρ⁺ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ₀↑ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γ γ↑ →
  Value V → No• V → No• N′ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ∣ suc Δᴸ ∣ Δᴿ ∣ ρ₀↑ ∣ γ↑
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ δ
    ⊢ᴺ Λ (substˣᵐ (↑ᵗᵐ τ) V) ⊑ substˣᵐ τ′ N′
      ⦂ `∀ A ⊑ B ∶ ν safe occ p
