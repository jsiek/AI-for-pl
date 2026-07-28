module
  proof.Quotient.NuImprecisionReductionClosedQuotientIdOnlyCastAudit
  where

-- File Charter:
--   * Proves that all four one-sided id-only cast rules are admissible in the
--     smaller ordinary relation by relaxing their coercion typing to the
--     ordinary tag-or-id cast mode.
--   * Shows that the smaller relation does not need polarity-specific
--     id-only cast constructors.
--   * Imports no live term-imprecision judgment and changes no relation.

open import CastImprecisionShape using
  (narrowing; widening; _⊢ᶜ_⦂_)
open import Coercions using
  (Coercion; id-onlyᵈ; id-only≤tag-or-idᵈ)
open import Imprecision using (ImpCtx)
open import ImprecisionComposition using
  (⌊_⌋; _；_≋_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  ; narrow-mode-relax
  ; widen-mode-relax
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( CtxImp
  )
open import proof.Core.Properties.CastImprecision using
  ( seal★-tag-or-id
  )
open import NuTerms using
  (Term; _⟨_⟩)
open import TermTyping using
  (cast-tag-or-id)
open import Types using
  (Ty; TyCtx)
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef


source-id-narrowingᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {c : Coercion} {s} →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  narrowing ⊢ᶜ c ⦂ s →
  s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q
source-id-narrowingᴿ c⊒ relation q c-shape composition =
  cast⊒⊑ᴿ cast-tag-or-id seal★-tag-or-id
    (narrow-mode-relax id-only≤tag-or-idᵈ c⊒)
    relation q c-shape composition


source-id-wideningᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {c : Coercion} {s} →
  id-onlyᵈ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⦂ B ⊑ B′ ∶ q
source-id-wideningᴿ c⊑ relation q c-shape composition =
  cast⊑⊑ᴿ cast-tag-or-id seal★-tag-or-id
    (widen-mode-relax id-only≤tag-or-idᵈ c⊑)
    relation q c-shape composition


target-id-narrowingᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A A′ B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {c′ : Coercion} {s} →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊒ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  narrowing ⊢ᶜ c′ ⦂ s →
  ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q
target-id-narrowingᴿ c′⊒ relation q c′-shape composition =
  ⊑cast⊒ᴿ cast-tag-or-id seal★-tag-or-id
    (narrow-mode-relax id-only≤tag-or-idᵈ c′⊒)
    relation q c′-shape composition


target-id-wideningᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A A′ B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {c′ : Coercion} {s} →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  widening ⊢ᶜ c′ ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
    ⊢ᴿ M ⊑ M′ ⟨ c′ ⟩ ⦂ A ⊑ B′ ∶ q
target-id-wideningᴿ c′⊑ relation q c′-shape composition =
  ⊑cast⊑ᴿ cast-tag-or-id seal★-tag-or-id
    (widen-mode-relax id-only≤tag-or-idᵈ c′⊑)
    relation q c′-shape composition
