module SourceConsistencyExamples where

-- File Charter:
--   * Records live regressions for crossable source-consistency variables.
--   * Checks the accepted calibration judgments, strict-slot gate rejection,
--     compilation, and blame/success execution of dynamic code inside
--     polymorphic source terms.
--   * Depends on the source language, consistency, compilation, and evaluator.

open import Data.Bool using (true)
open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TermCtx using (Z)
open import Consistency
open import GradualTerms
open import TyStore using (store-empty)
open import CastTerms
  using (Term; ⟨_,_,_⟩; _⊢_⦂_; _⟨_⟩; blame)
  renaming ($ to $ᶜ)
open import Reduction using (_—→_; tag-untag; tag-untag-bad)
open import Compile using (compile)
open import Primitives using (κℕ)
import Example as Ex

------------------------------------------------------------------------
-- Crossable program binders and strict consistency binders
------------------------------------------------------------------------

calibration-1 : idᶜ {Δ = 1} ⊢ ＇ Fin.zero ∼ ★
calibration-1 = total-to-★ (to★-★∼X∼★ refl)

strict-to-star-gate-impossible : ∀ {Δ} {μ : Env∼ Δ}
  → extᵐ μ ⊢ ＇ Fin.zero ∼★
  → ⊥
strict-to-star-gate-impossible (X∼★ᵍ ())
strict-to-star-gate-impossible (X∼★ᶜ ())

strict-from-star-gate-impossible : ∀ {Δ} {μ : Env∼ Δ}
  → extᵐ μ ⊢★∼ ＇ Fin.zero
  → ⊥
strict-from-star-gate-impossible (★∼Xᵍ ())
strict-from-star-gate-impossible (★∼Xᶜ ())

same-name-cross-redex : Term 1
same-name-cross-redex =
  ($ᶜ (κℕ 42) ⟨ (id {μ = idᶜ} (＇ Fin.zero)) ! ⟩)
    ⟨ ？ (id {μ = idᶜ} (＇ Fin.zero)) ⟩

same-name-cross-step : same-name-cross-redex —→ $ᶜ (κℕ 42)
same-name-cross-step =
  tag-untag
    ⦃ G∼★ = X∼★ᶜ refl ⦄ ⦃ ★∼G = ★∼Xᶜ refl ⦄
    ($ᶜ (κℕ 42))

different-name-cross-redex : Term 2
different-name-cross-redex =
  ($ᶜ (κℕ 42) ⟨ (id {μ = idᶜ} (＇ Fin.zero)) ! ⟩)
    ⟨ ？ (id {μ = idᶜ} (＇ (Fin.suc Fin.zero))) ⟩

different-name-cross-step : different-name-cross-redex —→ blame
different-name-cross-step =
  tag-untag-bad
    {G = ＇ Fin.zero} {H = ＇ (Fin.suc Fin.zero)}
    ⦃ G∼★ = X∼★ᶜ refl ⦄ ⦃ ★∼H = ★∼Xᶜ refl ⦄
    ($ᶜ (κℕ 42)) (λ ())

X⇒X : ∀ {Δ} → Ty (suc Δ)
X⇒X = ＇ Fin.zero ⇒ ＇ Fin.zero

∀X⇒X : Ty 0
∀X⇒X = `∀ X⇒X

calibration-3 : idᶜ {Δ = 0} ⊢ ∀X⇒X ∼ (★ ⇒ ★)
calibration-3 =
  inst_ ⦃ nonvar-fun ⦄ ⦃ ∈-fun-left var-∈ ⦄
    (total-from-★ (from★-★∼X refl) ↦
      total-to-★ (to★-X∼★ refl))
    (λ ())

left4-body : Ty 1
left4-body = ★ ⇒ (＇ Fin.zero ⇒ ★)

right4-body : Ty 1
right4-body = ＇ Fin.zero ⇒ (★ ⇒ ＇ Fin.zero)

calibration-4-body :
  genᵐ (instᵐ (idᶜ {Δ = 0}))
    ⊢ (★ ⇒ (＇ (Fin.suc Fin.zero) ⇒ ★))
    ∼ (＇ Fin.zero ⇒ (★ ⇒ ＇ Fin.zero))
calibration-4-body =
  total-to-★ (to★-X∼★ refl) ↦
    (total-from-★ (from★-★∼X refl) ↦
      total-from-★ (from★-★∼X refl))

calibration-4-gen :
  instᵐ (idᶜ {Δ = 0}) ⊢ left4-body ∼ ⇑ᵗ (`∀ right4-body)
calibration-4-gen =
  gen_ ⦃ nonvar-fun ⦄ ⦃ ∈-fun-left var-∈ ⦄
    calibration-4-body (λ ())

calibration-4 :
  idᶜ {Δ = 0} ⊢ (`∀ left4-body) ∼ (`∀ right4-body)
calibration-4 =
  inst_ ⦃ nonvar-fun ⦄
    ⦃ ∈-fun-right ∉-star (∈-fun-left var-∈) ⦄
    calibration-4-gen (λ ())

left5-body : Ty 2
left5-body = ＇ (Fin.suc Fin.zero) ⇒ ＇ Fin.zero

right5-body : Ty 2
right5-body = ★ ⇒ ＇ Fin.zero

calibration-5 :
  idᶜ {Δ = 1} ⊢ (`∀ left5-body) ∼ (`∀ right5-body)
calibration-5 =
  ∀ᶜ (total-from-★ (from★-★∼X∼★ refl) ↦ id (＇ Fin.zero))

------------------------------------------------------------------------
-- Dynamic code inside polymorphic source code
------------------------------------------------------------------------

minter : GTerm 0
minter =
  Λ (ƛ ＇ Fin.zero ⇒ ((ƛ ★ ⇒ ` 0) ·[ 0 ] ` 0))

minter-⊢ :
  0 ∣ [] ⊢ minter ⦂ `∀ (＇ Fin.zero ⇒ ★)
minter-⊢ =
  ⊢Λ {zero∈A = ∈-fun-left var-∈}
    (ƛ ＇ Fin.zero ⇒ ((ƛ ★ ⇒ ` 0) ·[ 0 ] ` 0))
    (⊢ƛ (⊢· (⊢ƛ (⊢` Z)) (⊢` Z)
      (total-from-★ (from★-★∼X∼★ refl))))

minter-compile :
  Σ[ N ∈ Term 0 ]
    ⟨ 0 , store-empty , [] ⟩ ⊢ N ⦂ `∀ (＇ Fin.zero ⇒ ★)
minter-compile = compile {Σ = store-empty} minter-⊢

ℕᵗ : Ty 0
ℕᵗ = ‵ `ℕ

minter-run : GTerm 0
minter-run =
  (ƛ ℕᵗ ⇒ ` 0) ·[ 1 ] ((minter `[ ℕᵗ ]) ·[ 0 ] $ (κℕ 42))

minter-run-⊢ : 0 ∣ [] ⊢ minter-run ⦂ ℕᵗ
minter-run-⊢ =
  ⊢·
    (⊢ƛ (⊢` Z))
    (⊢· (⊢• minter-⊢) (⊢$ (κℕ 42)) (id (‵ `ℕ)))
    (total-to-★ to★-ι)

minter-run-compile :
  Σ[ N ∈ Term 0 ] ⟨ 0 , store-empty , [] ⟩ ⊢ N ⦂ ℕᵗ
minter-run-compile = compile {Σ = store-empty} minter-run-⊢

minter-run-term : Term 0
minter-run-term = proj₁ minter-run-compile

minter-run-term-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ minter-run-term ⦂ ℕᵗ
minter-run-term-⊢ = proj₂ minter-run-compile

minter-run-blames :
  Ex.evalBlame Ex.gas minter-run-term-⊢ ≡ just true
minter-run-blames = refl

------------------------------------------------------------------------
-- Same-name round trip inside the polymorphic scope
------------------------------------------------------------------------

roundtrip : GTerm 0
roundtrip =
  Λ (ƛ ＇ Fin.zero ⇒
    ((ƛ ＇ Fin.zero ⇒ ` 0) ·[ 1 ]
      ((ƛ ★ ⇒ ` 0) ·[ 0 ] ` 0)))

roundtrip-⊢ :
  0 ∣ [] ⊢ roundtrip ⦂ `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)
roundtrip-⊢ =
  ⊢Λ {zero∈A = ∈-fun-left var-∈}
    (ƛ ＇ Fin.zero ⇒
      ((ƛ ＇ Fin.zero ⇒ ` 0) ·[ 1 ]
        ((ƛ ★ ⇒ ` 0) ·[ 0 ] ` 0)))
    (⊢ƛ
      (⊢·
        (⊢ƛ (⊢` Z))
        (⊢· (⊢ƛ (⊢` Z)) (⊢` Z)
          (total-from-★ (from★-★∼X∼★ refl)))
        (total-to-★ (to★-★∼X∼★ refl))))

roundtrip-run : GTerm 0
roundtrip-run = (roundtrip `[ ℕᵗ ]) ·[ 2 ] $ (κℕ 42)

roundtrip-run-⊢ : 0 ∣ [] ⊢ roundtrip-run ⦂ ℕᵗ
roundtrip-run-⊢ =
  ⊢· (⊢• roundtrip-⊢) (⊢$ (κℕ 42)) (id (‵ `ℕ))

roundtrip-run-compile :
  Σ[ N ∈ Term 0 ] ⟨ 0 , store-empty , [] ⟩ ⊢ N ⦂ ℕᵗ
roundtrip-run-compile = compile {Σ = store-empty} roundtrip-run-⊢

roundtrip-run-term : Term 0
roundtrip-run-term = proj₁ roundtrip-run-compile

roundtrip-run-term-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ roundtrip-run-term ⦂ ℕᵗ
roundtrip-run-term-⊢ = proj₂ roundtrip-run-compile

roundtrip-run-eval :
  Ex.evalNat Ex.gas roundtrip-run-term-⊢ ≡ just 42
roundtrip-run-eval = refl
