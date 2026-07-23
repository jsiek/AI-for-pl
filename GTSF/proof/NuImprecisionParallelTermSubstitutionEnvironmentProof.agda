module
  proof.NuImprecisionParallelTermSubstitutionEnvironmentProof
  where

-- File Charter:
--   * Projects a related quotiented substitution environment to the source
--     and target typing environments required by ordinary term substitution.
--   * Converts pointwise no-bullet evidence to the lookup-indexed form used by
--     the typing infrastructure.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import Data.List using ([]; _∷_)
open import ImprecisionWf using (ImpCtx)
open import NuTermImprecision using
  ( CtxImp
  ; StoreImp
  ; ctx-imp
  ; leftCtxⁱ
  ; leftStoreⁱ
  ; rightCtxⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (No•; Substˣ)
open import QuotientedTermImprecision using
  ( nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (S; TyCtx; Z; _∋_⦂_)
open import proof.TypePreservation using (SubstNo•; SubstWf)


quotiented-substitution-source-wfᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {τ τ′ : Substˣ} →
  (∀ {x A B p} →
    γ ∋ x ⦂ ctx-imp A B p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
      ⊢ᴺ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p) →
  SubstWf Δᴸ (leftStoreⁱ ρ) (leftCtxⁱ γ) (leftCtxⁱ δ) τ
quotiented-substitution-source-wfᵀ {γ = []} related ()
quotiented-substitution-source-wfᵀ
    {γ = ctx-imp A B p ∷ γ} related Z =
  nu-term-imprecision-source-typing (related Z)
quotiented-substitution-source-wfᵀ
    {γ = ctx-imp A B p ∷ γ} related (S x∈) =
  quotiented-substitution-source-wfᵀ
    (λ y∈ → related (S y∈)) x∈


quotiented-substitution-target-wfᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {γ δ : CtxImp Φ Δᴸ Δᴿ}
    {τ τ′ : Substˣ} →
  (∀ {x A B p} →
    γ ∋ x ⦂ ctx-imp A B p →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ δ
      ⊢ᴺ τ x ⊑ τ′ x ⦂ A ⊑ B ∶ p) →
  SubstWf Δᴿ (rightStoreⁱ ρ) (rightCtxⁱ γ)
    (rightCtxⁱ δ) τ′
quotiented-substitution-target-wfᵀ {γ = []} related ()
quotiented-substitution-target-wfᵀ
    {γ = ctx-imp A B p ∷ γ} related Z =
  nu-term-imprecision-target-typing (related Z)
quotiented-substitution-target-wfᵀ
    {γ = ctx-imp A B p ∷ γ} related (S x∈) =
  quotiented-substitution-target-wfᵀ
    (λ y∈ → related (S y∈)) x∈


pointwise-substitution-no•ᵀ :
  ∀ {γ τ} →
  (∀ x → No• (τ x)) →
  SubstNo• γ τ
pointwise-substitution-no•ᵀ noτ {x = x} x∈ = noτ x
