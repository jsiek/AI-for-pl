{-# OPTIONS --safe #-}

module proof.DGG.notes.PairedTargetInstantiationInputSquareCounterexample where

-- File Charter:
--   * Gives a closed counterexample to the proposed paired target
--     instantiation input square.
--   * Shows that an inert source all cast can change an arrow domain from
--     dynamic to natural while the target instantiation independently uses
--     the opposite dynamic-to-natural domain geometry.
--   * Justifies narrowing or removing that interface before target
--     instantiation catch-up is assembled.

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

import Data.Fin as Fin
open import Types
open import Consistency using
  (Env∼; idᶜ; extᵐ; instᵐ; _⊢_∼_; id; _!; _↦_; ∀ᶜ_;
   X∼★ᵍ)
open import CastTerms using (Inert; all)
import Imprecision as I
open import proof.DGG.World using (emptyᶜ; _⊑ᵀ⟨_⟩_)


ℂ ᴬ ᴮ′ : Ty 0
ℂ = `∀ (★ ⇒ ＇ Fin.zero)
ᴬ = `∀ (‵ `ℕ ⇒ ＇ Fin.zero)
ᴮ′ = ‵ `ℕ ⇒ ★

ᴮ : Ty 1
ᴮ = ★ ⇒ ＇ Fin.zero


ℕ! : ∀ {Δ} {ν : Env∼ Δ} → ν ⊢ ‵ `ℕ ∼ ★
ℕ! = id (‵ `ℕ) !

X! : ∀ {Δ} → instᵐ (idᶜ {Δ = Δ}) ⊢ ＇ Fin.zero ∼ ★
X! =
  _! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Ans = nonstar-X ⦄


source-all-consistency :
  idᶜ ⊢ ℂ ∼ ᴬ
source-all-consistency = ∀ᶜ (ℕ! ↦ id (＇ Fin.zero))

target-inst-consistency :
  instᵐ idᶜ ⊢ ᴮ ∼ ⇑ᵗ ᴮ′
target-inst-consistency = ℕ! ↦ X!


upper-input : ℂ ⊑ᵀ⟨ emptyᶜ ⟩ `∀ ᴮ
upper-input = I.∀⊑∀ (I.⇒⊑⇒ I.★⊑★ I.X⊑X)

lower-output : ᴬ ⊑ᵀ⟨ emptyᶜ ⟩ ᴮ′
lower-output =
  I.∀⊑ nonvar-fun (∈-fun-right ∉-base var-∈)
    (I.⇒⊑⇒ I.ι⊑ι (I.X⊑★ refl))


missing-edge : ℂ ⊑ᵀ⟨ emptyᶜ ⟩ ᴮ′ → ⊥
missing-edge (I.∀⊑ Cnv zero∈C (I.⇒⊑⇒ () codomain))


paired-target-instantiation-input-square-false :
  (Inert source-all-consistency
    → ᴮ′ ≢ ★
    → ℂ ⊑ᵀ⟨ emptyᶜ ⟩ `∀ ᴮ
    → ᴬ ⊑ᵀ⟨ emptyᶜ ⟩ ᴮ′
    → ℂ ⊑ᵀ⟨ emptyᶜ ⟩ ᴮ′)
  → ⊥
paired-target-instantiation-input-square-false square =
  missing-edge
    (square all (λ ()) upper-input lower-output)
