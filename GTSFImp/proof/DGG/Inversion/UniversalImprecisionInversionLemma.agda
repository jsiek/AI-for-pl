{-# OPTIONS --safe #-}

module proof.DGG.Inversion.UniversalImprecisionInversionLemma where

-- File Charter:
--   * Inverts imprecision between two universal types in the common center.
--   * Separates structural binders, source instantiation, and the bottom
--     universal clause while exposing their direct premises.
--   * Depends only on the type-imprecision definition.

open import Data.Fin using (zero)
import Data.Nat as Nat
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; NonVar; _∈ᵗ_; ★; `∀; ＇_; ⇑ᵗ)
import Imprecision as I


universal-imprecision-inversion : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A B : Ty (Nat.suc Δ)}
  → I._⊢_⊑_ μ (`∀ A) (`∀ B)
  → I._⊢_⊑_ (I.extᵐ μ) A B
    ⊎ (Σ[ non-var ∈ NonVar A ]
        Σ[ occurs ∈ zero ∈ᵗ A ]
          I._⊢_⊑_ (I.instᵐ μ) A (⇑ᵗ (`∀ B)))
    ⊎ ((A ≡ ＇ zero) × (B ≡ ★))
universal-imprecision-inversion (I.∀⊑∀ body) = inj₁ body
universal-imprecision-inversion (I.∀⊑ non-var occurs body) =
  inj₂ (inj₁ (non-var , occurs , body))
universal-imprecision-inversion I.bot-elim =
  inj₂ (inj₂ (refl , refl))
