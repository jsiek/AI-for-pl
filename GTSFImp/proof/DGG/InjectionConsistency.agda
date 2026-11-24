{-# OPTIONS --safe #-}

module proof.DGG.InjectionConsistency where

-- File Charter:
--   * Extends a consistency environment along an arbitrary finite injection.
--   * Preserves the original environment at every injected variable.
--   * Transports environment-indexed consistency along endpoint injections.
--   * Exports renameEnv∼ⁱ, rename∼ⁱ, and renameGenSafeⁱ; structural OPE
--     transport remains in Consistency.

open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero; suc)
import Data.Fin as Fin
import Data.Fin.Properties as FinP
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Types using (Ty; renameᵗ)
open import Consistency using (Env∼; idᶜ; _⊢_∼_)
import Consistency as C
open import CastTerms using (GenSafe)
import proof.Consistency as PC
open import proof.DGG.World using
  (Injectionᵗ; injectionᵗ; toRenameⁱ; toRenameⁱ-injective;
   fin-suc-injectiveⁱ)


private
  tailⁱ : ∀ {Δ Δ′}
    → Injectionᵗ (suc Δ) Δ′
    → Injectionᵗ Δ Δ′
  tailⁱ η = injectionᵗ
    (λ X → toRenameⁱ η (Fin.suc X))
    (λ eq → fin-suc-injectiveⁱ (toRenameⁱ-injective η eq))


renameEnv∼ⁱ : ∀ {Δ Δ′}
  → Injectionᵗ Δ Δ′
  → Env∼ Δ
  → Env∼ Δ′
renameEnv∼ⁱ {zero} η μ Z = idᶜ Z
renameEnv∼ⁱ {suc Δ} η μ Z
    with FinP._≟_ Z (toRenameⁱ η Fin.zero)
renameEnv∼ⁱ {suc Δ} η μ Z | yes eq = μ Fin.zero
renameEnv∼ⁱ {suc Δ} η μ Z | no neq =
  renameEnv∼ⁱ (tailⁱ η) (λ X → μ (Fin.suc X)) Z


private
  renameEnv∼ⁱ-preserves : ∀ {Δ Δ′}
      (η : Injectionᵗ Δ Δ′) (μ : Env∼ Δ) X
    → renameEnv∼ⁱ η μ (toRenameⁱ η X) ≡ μ X
  renameEnv∼ⁱ-preserves {zero} η μ ()
  renameEnv∼ⁱ-preserves {suc Δ} η μ Fin.zero
      with FinP._≟_ (toRenameⁱ η Fin.zero) (toRenameⁱ η Fin.zero)
  renameEnv∼ⁱ-preserves {suc Δ} η μ Fin.zero
      | yes eq = refl
  renameEnv∼ⁱ-preserves {suc Δ} η μ Fin.zero
      | no neq = ⊥-elim (neq refl)
  renameEnv∼ⁱ-preserves {suc Δ} η μ (Fin.suc X)
      with FinP._≟_ (toRenameⁱ η (Fin.suc X))
        (toRenameⁱ η Fin.zero)
  renameEnv∼ⁱ-preserves {suc Δ} η μ (Fin.suc X)
      | yes eq with toRenameⁱ-injective η eq
  renameEnv∼ⁱ-preserves {suc Δ} η μ (Fin.suc X)
      | yes eq | ()
  renameEnv∼ⁱ-preserves {suc Δ} η μ (Fin.suc X)
      | no neq = renameEnv∼ⁱ-preserves (tailⁱ η)
          (λ Y → μ (Fin.suc Y)) X


rename∼ⁱ : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
    (η : Injectionᵗ Δ Δ′)
  → μ ⊢ A ∼ B
  → renameEnv∼ⁱ η μ ⊢ renameᵗ (toRenameⁱ η) A ∼
      renameᵗ (toRenameⁱ η) B
rename∼ⁱ {μ = μ} η c =
  C.rename∼ (toRenameⁱ η) (renameEnv∼ⁱ-preserves η μ) c


renameGenSafeⁱ : ∀ {Δ Δ′} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (η : Injectionᵗ Δ Δ′)
  → GenSafe c
  → GenSafe (rename∼ⁱ η c)
renameGenSafeⁱ {μ = μ} η safe =
  PC.renameGenSafe (toRenameⁱ η) (renameEnv∼ⁱ-preserves η μ) safe
