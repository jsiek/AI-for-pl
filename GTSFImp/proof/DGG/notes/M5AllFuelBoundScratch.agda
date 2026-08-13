module proof.DGG.notes.M5AllFuelBoundScratch where

-- File Charter:
--   * Checks the smallest fuel bound needed by the M5 `allv-∀` spine.
--   * Exhibits a target universal cast whose opened body cast is not
--     strictly smaller than the outer instantiation cast.
--   * Records only the finite consistency witnesses; it changes no live
--     catch-up or imprecision surface.

import Data.Fin as Fin
open import Data.Nat using (suc; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (n<1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open import Types
open import Consistency
open import proof.Consistency using (castSize)


μ₀ : Env∼ 0
μ₀ ()


B₀ : Ty 1
B₀ = ＇ Fin.zero ⇒ `∀ ★


B₁ : Ty 1
B₁ = ＇ Fin.zero ⇒ ★


instance
  B₁-nonvar : NonVar B₁
  B₁-nonvar = nonvar-fun

  zero∈B₁ : Fin.zero ∈ᵗ B₁
  zero∈B₁ = ∈-fun-left var-∈


B′ : Ty 0
B′ = ★ ⇒ ★


B′≢★ : B′ ≢ ★
B′≢★ ()


d : extᵐ μ₀ ⊢ B₀ ∼ B₁
d = id (＇ Fin.zero) ↦
  _! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄
    (∀ᶜ (id ★)) ⦃ nonstar-∀ ⦄


c′ : instᵐ μ₀ ⊢ B₁ ∼ ⇑ᵗ B′
c′ =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄
      ⦃ ★∼G = ★∼Xᵍ refl ⦄
      (id (＇ Fin.zero)) ⦃ nonstar-X ⦄
  ↦ id ★


d-size : castSize d ≡ 5
d-size = refl


allocated-d : extᵐ (renameEnv∼ wk↪ᵗ μ₀) ⊢
    (＇ Fin.zero ⇒ `∀ ★) ∼ (＇ Fin.zero ⇒ ★)
allocated-d = id (＇ Fin.zero) ↦
  _! ⦃ Gᵍ = ∀★ ⦄ ⦃ G∼★ = ∀∼★ ⦄
    (∀ᶜ (id ★)) ⦃ nonstar-∀ ⦄


opened-d-size : castSize
    (allocated-d [ ＇ Fin.zero ]ᶜ) ≡ 5
opened-d-size = refl


c′-size : castSize c′ ≡ 4
c′-size = refl


outer-size : castSize ((inst c′) B′≢★) ≡ 5
outer-size = refl


outer-fits-minimal-fuel :
  castSize ((inst c′) B′≢★) < 6
outer-fits-minimal-fuel = n<1+n 5


opened-spine-does-not-fit : ¬ (suc (castSize d) < 6)
opened-spine-does-not-fit
    (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))


stored-cast-not-bounded-by-inst-body : ¬ (castSize d ≤ castSize c′)
stored-cast-not-bounded-by-inst-body
    (s≤s (s≤s (s≤s (s≤s ()))))
