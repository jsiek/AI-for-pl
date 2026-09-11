{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.WorldChangeSequenceProbe where

-- File Charter:
--   * Checks that the live World history has only empty and snoc cases.
--   * Computes the exact change counts for the allocation worlds used by
--     Examples 4 and 12 without introducing a mirror world relation.
--   * Leaves source-rebase behavior to WorldCurrentEmbeddingProbe.

open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (★; ＇_; ‵_; `ℕ)
open import TyStore using (store-empty)
import Imprecision as I
open import CastTerms using (Ctx; ⟨_,_,_⟩; _,ˢ_; ⇑ᵉᵗ)
open import proof.DGG.World


change-count : ∀ {Γᴸ Γᴿ} → Γᴸ ⊑ᶜ Γᴿ → ℕ
change-count emptyᶜ = zero
change-count (γ ▻ᶜ change) = suc (change-count γ)


base : Ctx
base = ⟨ 0 , store-empty , [] ⟩

example4-world : (base ,ˢ ‵ `ℕ) ⊑ᶜ (base ,ˢ ★)
example4-world = bindBothStarᶜ emptyᶜ I.ι⊑★ (λ ())

example4-change-count : change-count example4-world ≡ 1
example4-change-count = refl


example12-alpha-world : base ⊑ᶜ (base ,ˢ ★)
example12-alpha-world = bindRightᶜ emptyᶜ ★ (inj₁ refl)

example12-alpha-change-count : change-count example12-alpha-world ≡ 1
example12-alpha-change-count = refl

example12-beta-fresh :
  RightBindFreshᶜ example12-alpha-world (＇ Fin.zero)
example12-beta-fresh =
  inj₂ (Fin.suc Fin.zero , refl , λ ())

example12-beta-world :
  base ⊑ᶜ ((base ,ˢ ★) ,ˢ ＇ Fin.zero)
example12-beta-world =
  bindRightᶜ example12-alpha-world (＇ Fin.zero) example12-beta-fresh

example12-beta-change-count : change-count example12-beta-world ≡ 2
example12-beta-change-count = refl

example12-c1-world :
  ⇑ᵉᵗ base ⊑ᶜ ((base ,ˢ ★) ,ˢ ＇ Fin.zero)
example12-c1-world = liftLeftᶜ example12-beta-world

example12-c1-change-count : change-count example12-c1-world ≡ 3
example12-c1-change-count = refl

example12-c5-world :
  (base ,ˢ ‵ `ℕ) ⊑ᶜ
    (((base ,ˢ ★) ,ˢ ＇ Fin.zero) ,ˢ ‵ `ℕ)
example12-c5-world =
  bindBothStarᶜ example12-beta-world I.ι⊑ι (λ ())

example12-c5-change-count : change-count example12-c5-world ≡ 3
example12-c5-change-count = refl
