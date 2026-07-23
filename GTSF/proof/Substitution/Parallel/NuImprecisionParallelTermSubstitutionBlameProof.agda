module proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionBlameProof where

-- File Charter:
--   * Proves the blame-source root of prefix-aware parallel substitution.
--   * Weakens the target typing through the store prefix, then applies typed
--     parallel substitution.
--   * Contains no relation recursion, postulate, hole, or permissive option.

open import Data.Nat.Properties using (≤-refl)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  ( CtxImp
  ; StoreImp
  ; ctx-imp
  ; rightCtxⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (No•; Substˣ; Term; blame; substˣᵐ)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; blame⊑ᵀ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty; TyCtx; _∋_⦂_)
open import
  proof.Substitution.Parallel.NuImprecisionParallelTermSubstitutionEnvironmentProof
  using
  ( pointwise-substitution-no•ᵀ
  ; quotiented-substitution-target-wfᵀ
  )
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (rightStoreⁱ-prefix-inclusion)
open import proof.Core.Properties.TypePreservation using (term-weaken; typing-substˣ)


quotiented-parallel-term-substitution-blame-proofᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {τ τ′ : Substˣ} {M′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (prefix : StoreImpPrefix ρ₀ ρ⁺) →
  (related : ∀ {x C C′ q} →
    γ ∋ x ⦂ ctx-imp C C′ q →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ δ
      ⊢ᴺ τ x ⊑ τ′ x ⦂ C ⊑ C′ ∶ q) →
  (∀ x → No• (τ′ x)) →
  No• M′ →
  Δᴿ ∣ rightStoreⁱ ρ₀ ∣ rightCtxⁱ γ ⊢ M′ ⦂ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ⁺ ∣ δ
    ⊢ᴺ substˣᵐ τ blame ⊑ substˣᵐ τ′ M′
    ⦂ A ⊑ B ∶ p
quotiented-parallel-term-substitution-blame-proofᵀ
    prefix related noτ′ noM′ M′⊢ =
  blame⊑ᵀ
    (typing-substˣ
      (quotiented-substitution-target-wfᵀ related)
      (pointwise-substitution-no•ᵀ noτ′)
      noM′
      (term-weaken ≤-refl
        (rightStoreⁱ-prefix-inclusion prefix) noM′ M′⊢))
