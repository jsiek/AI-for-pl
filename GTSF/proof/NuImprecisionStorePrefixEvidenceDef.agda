module proof.NuImprecisionStorePrefixEvidenceDef where

-- File Charter:
--   * States preservation of store-indexed quotiented-imprecision evidence
--     through a relational-store prefix.
--   * Covers stored/linked correspondence, paired casts, and quotient
--     widening pairs without transporting any term relation.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Coercions using (Coercion)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  (StoreCorresponds; StoreImp)
open import QuotientedTermImprecision using
  ( PairedCast
  ; QuotientWideningPair
  ; StoreImpPrefix
  )
open import Types using (Ty; TyCtx; TyVar)


StoreCorrespondsPrefixᵀ : Set
StoreCorrespondsPrefixᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {α β : TyVar} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  StoreCorresponds ρ₀ α A β B p →
  StoreCorresponds ρ⁺ α A β B p


PairedCastPrefixᵀ : Set₁
PairedCastPrefixᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {c c′ : Coercion} {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  PairedCast Φ Δᴸ Δᴿ ρ₀ c c′ p q →
  PairedCast Φ Δᴸ Δᴿ ρ⁺ c c′ p q


QuotientWideningPairPrefixᵀ : Set₁
QuotientWideningPairPrefixᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {u u′ : Coercion} {D D′ A A′ : Ty} →
  StoreImpPrefix ρ₀ ρ⁺ →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  QuotientWideningPair Δᴸ Δᴿ ρ⁺ u u′ D D′ A A′
