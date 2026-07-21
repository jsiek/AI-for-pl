module proof.NuImprecisionWorldCoherentSourceOneStepPrefixProof where

-- File Charter:
--   * Specializes ambient-prefix exact source one-step simulation to the
--     current relational store.
--   * Derives the two ambient typing premises from the quotient relation.
--   * Connects the recursive prefix worker to the exact top-level engine.
--   * Contains no recursive dispatcher, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  ( StoreImp
  ; leftCtxⁱ
  ; leftStoreⁱ
  ; rightCtxⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; nu-term-imprecision-source-typing
  ; nu-term-imprecision-target-typing
  ; prefix-reflⁱ
  )
open import proof.NuImprecisionWorldCoherentSourceOneStepPrefixDef using
  (WorldCoherentSourceOneStepPrefixᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentExactSourceOneStepSimulationᵀ)
open import TermTyping using (_∣_∣_⊢_⦂_)


normalize-source-one-step-empty-runtime-context :
  ∀ {Δ Σ Γ M A} →
  Γ ≡ [] →
  Δ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A
normalize-source-one-step-empty-runtime-context refl M⊢ = M⊢


source-one-step-empty-context-source-typing :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A
source-one-step-empty-context-source-typing
    {Φ} {Δᴸ} {Δᴿ} {M} {M′} {A} {B} {ρ} {p} M⊑M′ =
  normalize-source-one-step-empty-runtime-context
    {Γ = leftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} []} refl
    (nu-term-imprecision-source-typing
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γ = []}
      {M = M} {M′ = M′} {A = A} {B = B} {p = p} M⊑M′)


source-one-step-empty-context-target-typing :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ B
source-one-step-empty-context-target-typing
    {Φ} {Δᴸ} {Δᴿ} {M} {M′} {A} {B} {ρ} {p} M⊑M′ =
  normalize-source-one-step-empty-runtime-context
    {Γ = rightCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} []} refl
    (nu-term-imprecision-target-typing
      {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {ρ = ρ} {γ = []}
      {M = M} {M′ = M′} {A = A} {B = B} {p = p} M⊑M′)


world-coherent-exact-source-one-step-prefix-proofᵀ :
  WorldCoherentSourceOneStepPrefixᵀ →
  WorldCoherentExactSourceOneStepSimulationᵀ
world-coherent-exact-source-one-step-prefix-proofᵀ
    prefix-step coherent exclusive wfL wfR okM okM′ M⊑M′ source-step =
  prefix-step prefix-reflⁱ coherent exclusive wfL wfR okM okM′
    (source-one-step-empty-context-source-typing M⊑M′)
    (source-one-step-empty-context-target-typing M⊑M′)
    M⊑M′ source-step
