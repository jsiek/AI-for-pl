module proof.InterpreterStaticPrefix where

-- File Charter:
--   * Weakens no-bullet static term narrowing through a relational-store
--     prefix.
--   * Reconstructs the proof-only allocation wrapper from pure typing
--     weakening and endpoint typing projections.
--   * Contains no interpreter semantics or reduction dependency.

open import Data.Nat.Properties using (≤-refl)

open import NuTermImprecision using (CtxImp; StoreImp)
open import NuTerms using (No•; Term)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; allocation-prefixᵀ
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  )
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.InterpreterTermTypingWeakening using
  (refined-term-weaken)

static-prefix-weaken :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {γ : CtxImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  No• M →
  No• M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ γ
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p
static-prefix-weaken prefix noM noM′ terms =
  allocation-prefixᵀ prefix terms
    (refined-term-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) noM
      (nu-term-imprecision-source-typing terms))
    (refined-term-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) noM′
      (nu-term-imprecision-target-typing terms))
