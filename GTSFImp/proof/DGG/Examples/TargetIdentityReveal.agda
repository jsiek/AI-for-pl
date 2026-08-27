{-# OPTIONS --safe #-}

module proof.DGG.Examples.TargetIdentityReveal where

-- File Charter:
--   * Checks the target-only counterpart of SourceIdentityReveal.
--   * Uses the source-level annotated-identity idiom to make the ordinary
--     compiler cast a polymorphic value at `∀ X. X ⇒ ★` to `★ ⇒ ★`.
--   * Records one simulation checkpoint after every more-precise reduction;
--     target catch-up exposes structural-identity target reveals.

import Data.Fin as Fin
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
import Data.Maybe
import Data.Nat as Nat
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TermCtx using (Z)
open import Consistency
open import GradualTerms renaming (_∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_)
import GradualTermImprecision as GTI
import Imprecision as I
open import TyStore using
  (store-empty; store-bind; _∋_⦂_; Z∋; S-bind∋)
import Conversion as Conv
open import Conversion using (seal; unseal; _↦↑_)
open import CastTerms using
  (Ctx; Term; ⟨_,_,_⟩; _,ˢ_; ⇑ᵉᵗ; _⊢_⦂_)
import CastTerms as C
open import Compile using (compile)
open import Primitives using (κℕ)
open import Reduction using
  (keep; bind; applyEnv; applyConsistency; []; _∷_; _—↠[_]_; _—→[_]⟨_⟩_;
   _∎[])
open import Eval using (step?)
import Example as Ex
import proof.DGG.OneStep as Step
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.World
open import proof.DGG.SourceRebase using (source-rebase-now)
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition;
   concealGeneratorPosition)
open import proof.DGG.ImpLadder using (impLadderDefault)

open GTI using () renaming
  (_∣_⊢ᴳ_⊑_⦂_⊑_∶_ to _∣_⊢ᴳ²_⊑_⦂_⊑_∶_)

------------------------------------------------------------------------
-- Types, source programs, and source evidence
------------------------------------------------------------------------

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

Xᵗ : ∀ {Δ} → Ty (Nat.suc Δ)
Xᵗ = ＇ Fin.zero

X⇒★ : ∀ {Δ} → Ty (Nat.suc Δ)
X⇒★ = Xᵗ ⇒ ★

∀X⇒★ : ∀ {Δ} → Ty Δ
∀X⇒★ = `∀ X⇒★

dynamic-function : ∀ {Δ} → Ty Δ
dynamic-function = ★ ⇒ ★

X∈X⇒★ : ∀ {Δ} → Fin.zero ∈ᵗ X⇒★ {Δ}
X∈X⇒★ = ∈-fun-left var-∈

flip-inst-★?X : ∀ {Δ} {μ : Env∼ Δ}
  → flipᵐ (instᵐ μ) ⊢ ★ ∼ Xᵗ
flip-inst-★?X =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Bns = nonstar-X ⦄

∀X⇒★∼★⇒★ : ∀ {Δ} → ∀X⇒★ {Δ} ∼ dynamic-function
∀X⇒★∼★⇒★ =
  inst_ ⦃ Anv = nonvar-fun ⦄ ⦃ z∈A = X∈X⇒★ ⦄
    (flip-inst-★?X ↦ id ★) (λ ())

★⇒★∼∀X⇒★ : ∀ {Δ} → dynamic-function {Δ} ∼ ∀X⇒★
★⇒★∼∀X⇒★ = symᶜ ∀X⇒★∼★⇒★

∀X⇒★∼∀X⇒★ : ∀ {Δ} → ∀X⇒★ {Δ} ∼ ∀X⇒★
∀X⇒★∼∀X⇒★ = ∀ᶜ (id (＇ Fin.zero) ↦ id ★)

nat-consistent-star : ∀ {Δ} → ℕᵗ {Δ} ∼ ★
nat-consistent-star = total-to-★ to★-ι

star-consistent-X : ∀ {Δ} → ★ ∼ Xᵗ {Δ}
star-consistent-X = total-from-★ (from★-★∼X∼★ refl)

ℓ-body : Label
ℓ-body = 0

ℓ-cast : Label
ℓ-cast = 1

ℓ-result : Label
ℓ-result = 2

ℓ-outer : Label
ℓ-outer = 3

more-precise : GTerm 0
more-precise =
  (ƛ ℕᵗ ⇒ ` 0) ·[ ℓ-outer ]
    ((((ƛ ∀X⇒★ ⇒ ` 0) ·[ ℓ-cast ]
        (Λ (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))))
      `[ ℕᵗ ]) ·[ ℓ-result ] $ (κℕ 42))

less-precise : GTerm 0
less-precise =
  (ƛ ℕᵗ ⇒ ` 0) ·[ ℓ-outer ]
    (((ƛ dynamic-function ⇒ ` 0) ·[ ℓ-cast ]
        (Λ (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))))
      ·[ ℓ-result ] $ (κℕ 42))

poly-⊢ : 0 ∣ [] ⊢ᴳ
  Λ (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0)) ⦂ ∀X⇒★
poly-⊢ =
  ⊢Λ {zero∈A = X∈X⇒★}
    (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))
    (⊢ƛ (⊢· (⊢ƛ (⊢` Z)) (⊢` Z)
      (total-from-★ (from★-★∼X∼★ refl))))

more-core-⊢ : 0 ∣ [] ⊢ᴳ
  ((((ƛ ∀X⇒★ ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))))
    `[ ℕᵗ ]) ·[ ℓ-result ] $ (κℕ 42)) ⦂ ★
more-core-⊢ =
  ⊢·
    (⊢• (⊢· (⊢ƛ (⊢` Z)) poly-⊢ ∀X⇒★∼∀X⇒★))
    (⊢$ (κℕ 42))
    (id (‵ `ℕ))

less-core-⊢ : 0 ∣ [] ⊢ᴳ
  (((ƛ dynamic-function ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))))
    ·[ ℓ-result ] $ (κℕ 42)) ⦂ ★
less-core-⊢ =
  ⊢·
    (⊢· (⊢ƛ (⊢` Z)) poly-⊢ ★⇒★∼∀X⇒★)
    (⊢$ (κℕ 42))
    (symᶜ nat-consistent-star)

more-precise-⊢ : 0 ∣ [] ⊢ᴳ more-precise ⦂ ℕᵗ
more-precise-⊢ =
  ⊢· (⊢ƛ (⊢` Z)) more-core-⊢ nat-consistent-star

less-precise-⊢ : 0 ∣ [] ⊢ᴳ less-precise ⦂ ℕᵗ
less-precise-⊢ =
  ⊢· (⊢ƛ (⊢` Z)) less-core-⊢ nat-consistent-star

X⇒★⊑X⇒★ : ∀ {Δ} {μ : I.ImpEnv (Nat.suc Δ)}
  → μ I.⊢ X⇒★ ⊑ X⇒★
X⇒★⊑X⇒★ = I.⇒⊑⇒ I.X⊑X I.★⊑★

∀X⇒★⊑∀X⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ∀X⇒★ ⊑ ∀X⇒★
∀X⇒★⊑∀X⇒★ = I.∀⊑∀ X⇒★⊑X⇒★

∀X⇒★⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ∀X⇒★ ⊑ dynamic-function
∀X⇒★⊑★⇒★ =
  I.∀⊑ nonvar-fun X∈X⇒★
    (I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★)

ℕ⇒★⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ (ℕᵗ ⇒ ★) ⊑ dynamic-function
ℕ⇒★⊑★⇒★ = I.⇒⊑⇒ I.ι⊑★ I.★⊑★

poly-imprecision :
  I.idᵐ {Δ = 0} ∣ [] ⊢ᴳ²
    Λ (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))
    ⊑ Λ (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))
    ⦂ ∀X⇒★ ⊑ ∀X⇒★ ∶ ∀X⇒★⊑∀X⇒★
poly-imprecision =
  GTI.Λ⊑Λᴳ {p = X⇒★⊑X⇒★} GTI.lift-[]
    (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))
    (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))
    X∈X⇒★ X∈X⇒★
    (GTI.ƛ⊑ƛᴳ
      (GTI.·⊑·ᴳ
        (GTI.ƛ⊑ƛᴳ {pA = I.★⊑★} {pB = I.★⊑★}
          (GTI.x⊑xᴳ GTI.Zⁱ))
        (GTI.x⊑xᴳ GTI.Zⁱ)
        (total-from-★ (from★-★∼X∼★ refl))
        (total-from-★ (from★-★∼X∼★ refl))))

cast-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ²
    ((ƛ ∀X⇒★ ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))))
    ⊑ ((ƛ dynamic-function ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))))
    ⦂ ∀X⇒★ ⊑ dynamic-function ∶ ∀X⇒★⊑★⇒★
cast-imprecision =
  GTI.·⊑·ᴳ
    (GTI.ƛ⊑ƛᴳ {pA = ∀X⇒★⊑★⇒★} {pB = ∀X⇒★⊑★⇒★}
      (GTI.x⊑xᴳ GTI.Zⁱ))
    poly-imprecision
    ∀X⇒★∼∀X⇒★ ★⇒★∼∀X⇒★

core-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ²
    ((((ƛ ∀X⇒★ ⇒ ` 0) ·[ ℓ-cast ]
        (Λ (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))))
      `[ ℕᵗ ]) ·[ ℓ-result ] $ (κℕ 42))
    ⊑ (((ƛ dynamic-function ⇒ ` 0) ·[ ℓ-cast ]
        (Λ (ƛ Xᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-body ] ` 0))))
      ·[ ℓ-result ] $ (κℕ 42))
    ⦂ ★ ⊑ ★ ∶ I.★⊑★
core-imprecision =
  GTI.·⊑·ᴳ
    (GTI.[]⊑ᴳ cast-imprecision I.ι⊑★ ℕ⇒★⊑★⇒★)
    (GTI.κ⊑κᴳ (κℕ 42))
    (id (‵ `ℕ)) (symᶜ nat-consistent-star)

source-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ² more-precise ⊑ less-precise
    ⦂ ℕᵗ ⊑ ℕᵗ ∶ I.ι⊑ι
source-imprecision =
  GTI.·⊑·ᴳ
    (GTI.ƛ⊑ƛᴳ {pA = I.ι⊑ι} {pB = I.ι⊑ι}
      (GTI.x⊑xᴳ GTI.Zⁱ))
    core-imprecision nat-consistent-star nat-consistent-star


------------------------------------------------------------------------
-- Ordinary compiler outputs
------------------------------------------------------------------------

more-precise-compiled : Term 0
more-precise-compiled =
  proj₁ (compile {Σ = store-empty} more-precise-⊢)

more-precise-compiled-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ more-precise-compiled ⦂ ℕᵗ
more-precise-compiled-⊢ =
  proj₂ (compile {Σ = store-empty} more-precise-⊢)

less-precise-compiled : Term 0
less-precise-compiled =
  proj₁ (compile {Σ = store-empty} less-precise-⊢)

less-precise-compiled-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ less-precise-compiled ⦂ ℕᵗ
less-precise-compiled-⊢ =
  proj₂ (compile {Σ = store-empty} less-precise-⊢)

more-precise-eval :
  Ex.evalBlame Ex.gas more-precise-compiled-⊢ ≡ Data.Maybe.just true
more-precise-eval = refl

less-precise-eval :
  Ex.evalBlame Ex.gas less-precise-compiled-⊢ ≡ Data.Maybe.just true
less-precise-eval = refl


------------------------------------------------------------------------
-- More-precise executable checkpoints
------------------------------------------------------------------------

more-checkpoint₀ : Term 0
more-checkpoint₀ = more-precise-compiled

more-store₀ = store-empty

more-step₀ : Step.OneStep more-store₀ more-checkpoint₀
more-step₀ = Step.from-just-step (step? more-store₀ more-checkpoint₀) refl

more-checkpoint₁ : Term (Step.Δ′ more-step₀)
more-checkpoint₁ = Step.next more-step₀

more-store₁ = Step.store-after more-step₀

more-step₁ : Step.OneStep more-store₁ more-checkpoint₁
more-step₁ = Step.from-just-step (step? more-store₁ more-checkpoint₁) refl

more-checkpoint₂ : Term (Step.Δ′ more-step₁)
more-checkpoint₂ = Step.next more-step₁

more-store₂ = Step.store-after more-step₁

more-step₂ : Step.OneStep more-store₂ more-checkpoint₂
more-step₂ = Step.from-just-step (step? more-store₂ more-checkpoint₂) refl

more-checkpoint₃ : Term (Step.Δ′ more-step₂)
more-checkpoint₃ = Step.next more-step₂

more-store₃ = Step.store-after more-step₂

more-step₃ : Step.OneStep more-store₃ more-checkpoint₃
more-step₃ = Step.from-just-step (step? more-store₃ more-checkpoint₃) refl

more-checkpoint₄ : Term (Step.Δ′ more-step₃)
more-checkpoint₄ = Step.next more-step₃

more-store₄ = Step.store-after more-step₃

more-step₄ : Step.OneStep more-store₄ more-checkpoint₄
more-step₄ = Step.from-just-step (step? more-store₄ more-checkpoint₄) refl

more-checkpoint₅ : Term (Step.Δ′ more-step₄)
more-checkpoint₅ = Step.next more-step₄

more-store₅ = Step.store-after more-step₄

more-step₅ : Step.OneStep more-store₅ more-checkpoint₅
more-step₅ = Step.from-just-step (step? more-store₅ more-checkpoint₅) refl

more-checkpoint₆ : Term (Step.Δ′ more-step₅)
more-checkpoint₆ = Step.next more-step₅

more-store₆ = Step.store-after more-step₅

more-step₆ : Step.OneStep more-store₆ more-checkpoint₆
more-step₆ = Step.from-just-step (step? more-store₆ more-checkpoint₆) refl

more-checkpoint₇ : Term (Step.Δ′ more-step₆)
more-checkpoint₇ = Step.next more-step₆

more-store₇ = Step.store-after more-step₆

more-step₇ : Step.OneStep more-store₇ more-checkpoint₇
more-step₇ = Step.from-just-step (step? more-store₇ more-checkpoint₇) refl

more-checkpoint₈ : Term (Step.Δ′ more-step₇)
more-checkpoint₈ = Step.next more-step₇

more-store₈ = Step.store-after more-step₇

more-step₈ : Step.OneStep more-store₈ more-checkpoint₈
more-step₈ = Step.from-just-step (step? more-store₈ more-checkpoint₈) refl

more-checkpoint₉ : Term (Step.Δ′ more-step₈)
more-checkpoint₉ = Step.next more-step₈

more-store₉ = Step.store-after more-step₈

more-step₉ : Step.OneStep more-store₉ more-checkpoint₉
more-step₉ = Step.from-just-step (step? more-store₉ more-checkpoint₉) refl

more-checkpoint₁₀ : Term (Step.Δ′ more-step₉)
more-checkpoint₁₀ = Step.next more-step₉

more-store₁₀ = Step.store-after more-step₉

more-step₁₀ : Step.OneStep more-store₁₀ more-checkpoint₁₀
more-step₁₀ = Step.from-just-step (step? more-store₁₀ more-checkpoint₁₀) refl

more-checkpoint₁₁ : Term (Step.Δ′ more-step₁₀)
more-checkpoint₁₁ = Step.next more-step₁₀

more-store₁₁ = Step.store-after more-step₁₀


------------------------------------------------------------------------
-- Less-precise executable trace
------------------------------------------------------------------------

less-step-term₀ : Term 0
less-step-term₀ = less-precise-compiled

less-step-store₀ = store-empty

less-step₀ : Step.OneStep less-step-store₀ less-step-term₀
less-step₀ = Step.from-just-step (step? less-step-store₀ less-step-term₀) refl

less-step-term₁ : Term (Step.Δ′ less-step₀)
less-step-term₁ = Step.next less-step₀

less-step-store₁ = Step.store-after less-step₀

less-step₁ : Step.OneStep less-step-store₁ less-step-term₁
less-step₁ = Step.from-just-step (step? less-step-store₁ less-step-term₁) refl

less-step-term₂ : Term (Step.Δ′ less-step₁)
less-step-term₂ = Step.next less-step₁

less-step-store₂ = Step.store-after less-step₁

less-step₂ : Step.OneStep less-step-store₂ less-step-term₂
less-step₂ = Step.from-just-step (step? less-step-store₂ less-step-term₂) refl

less-step-term₃ : Term (Step.Δ′ less-step₂)
less-step-term₃ = Step.next less-step₂

less-step-store₃ = Step.store-after less-step₂

less-step₃ : Step.OneStep less-step-store₃ less-step-term₃
less-step₃ = Step.from-just-step (step? less-step-store₃ less-step-term₃) refl

less-step-term₄ : Term (Step.Δ′ less-step₃)
less-step-term₄ = Step.next less-step₃

less-step-store₄ = Step.store-after less-step₃

less-step₄ : Step.OneStep less-step-store₄ less-step-term₄
less-step₄ = Step.from-just-step (step? less-step-store₄ less-step-term₄) refl

less-step-term₅ : Term (Step.Δ′ less-step₄)
less-step-term₅ = Step.next less-step₄

less-step-store₅ = Step.store-after less-step₄

less-step₅ : Step.OneStep less-step-store₅ less-step-term₅
less-step₅ = Step.from-just-step (step? less-step-store₅ less-step-term₅) refl

less-step-term₆ : Term (Step.Δ′ less-step₅)
less-step-term₆ = Step.next less-step₅

less-step-store₆ = Step.store-after less-step₅

less-step₆ : Step.OneStep less-step-store₆ less-step-term₆
less-step₆ = Step.from-just-step (step? less-step-store₆ less-step-term₆) refl

less-step-term₇ : Term (Step.Δ′ less-step₆)
less-step-term₇ = Step.next less-step₆

less-step-store₇ = Step.store-after less-step₆

less-step₇ : Step.OneStep less-step-store₇ less-step-term₇
less-step₇ = Step.from-just-step (step? less-step-store₇ less-step-term₇) refl

less-step-term₈ : Term (Step.Δ′ less-step₇)
less-step-term₈ = Step.next less-step₇

less-step-store₈ = Step.store-after less-step₇

less-step₈ : Step.OneStep less-step-store₈ less-step-term₈
less-step₈ = Step.from-just-step (step? less-step-store₈ less-step-term₈) refl

less-step-term₉ : Term (Step.Δ′ less-step₈)
less-step-term₉ = Step.next less-step₈

less-step-store₉ = Step.store-after less-step₈

less-step₉ : Step.OneStep less-step-store₉ less-step-term₉
less-step₉ = Step.from-just-step (step? less-step-store₉ less-step-term₉) refl

less-step-term₁₀ : Term (Step.Δ′ less-step₉)
less-step-term₁₀ = Step.next less-step₉

less-step-store₁₀ = Step.store-after less-step₉

less-step₁₀ : Step.OneStep less-step-store₁₀ less-step-term₁₀
less-step₁₀ =
  Step.from-just-step (step? less-step-store₁₀ less-step-term₁₀) refl

less-step-term₁₁ : Term (Step.Δ′ less-step₁₀)
less-step-term₁₁ = Step.next less-step₁₀

less-step-store₁₁ = Step.store-after less-step₁₀

less-step₁₁ : Step.OneStep less-step-store₁₁ less-step-term₁₁
less-step₁₁ =
  Step.from-just-step (step? less-step-store₁₁ less-step-term₁₁) refl

less-step-term₁₂ : Term (Step.Δ′ less-step₁₁)
less-step-term₁₂ = Step.next less-step₁₁

less-step-store₁₂ = Step.store-after less-step₁₁

more-step₁₁ : Step.OneStep more-store₁₁ more-checkpoint₁₁
more-step₁₁ = Step.from-just-step (step? more-store₁₁ more-checkpoint₁₁) refl

more-checkpoint₁₂ : Term (Step.Δ′ more-step₁₁)
more-checkpoint₁₂ = Step.next more-step₁₁

more-store₁₂ = Step.store-after more-step₁₁

more-step₁₂ : Step.OneStep more-store₁₂ more-checkpoint₁₂
more-step₁₂ = Step.from-just-step (step? more-store₁₂ more-checkpoint₁₂) refl

more-checkpoint₁₃ : Term (Step.Δ′ more-step₁₂)
more-checkpoint₁₃ = Step.next more-step₁₂

more-store₁₃ = Step.store-after more-step₁₂

less-step₁₂ : Step.OneStep less-step-store₁₂ less-step-term₁₂
less-step₁₂ =
  Step.from-just-step (step? less-step-store₁₂ less-step-term₁₂) refl

less-step-term₁₃ : Term (Step.Δ′ less-step₁₂)
less-step-term₁₃ = Step.next less-step₁₂

less-step-store₁₃ = Step.store-after less-step₁₂

less-step₁₃ : Step.OneStep less-step-store₁₃ less-step-term₁₃
less-step₁₃ =
  Step.from-just-step (step? less-step-store₁₃ less-step-term₁₃) refl

less-step-term₁₄ : Term (Step.Δ′ less-step₁₃)
less-step-term₁₄ = Step.next less-step₁₃

less-step-store₁₄ = Step.store-after less-step₁₃


------------------------------------------------------------------------
-- Paired checkpoints and whole-term reduction segments
------------------------------------------------------------------------

less-checkpoint₀ : Term 0
less-checkpoint₀ = less-step-term₀

less-checkpoint₁ : Term (Step.Δ′ less-step₂)
less-checkpoint₁ = less-step-term₃

less-checkpoint₂ : Term (Step.Δ′ less-step₂)
less-checkpoint₂ = less-step-term₃

less-checkpoint₃ : Term (Step.Δ′ less-step₂)
less-checkpoint₃ = less-step-term₃

less-checkpoint₄ : Term (Step.Δ′ less-step₂)
less-checkpoint₄ = less-step-term₃

less-checkpoint₅ : Term (Step.Δ′ less-step₃)
less-checkpoint₅ = less-step-term₄

less-checkpoint₆ : Term (Step.Δ′ less-step₄)
less-checkpoint₆ = less-step-term₅

less-checkpoint₇ : Term (Step.Δ′ less-step₅)
less-checkpoint₇ = less-step-term₆

less-checkpoint₈ : Term (Step.Δ′ less-step₇)
less-checkpoint₈ = less-step-term₈

less-checkpoint₉ : Term (Step.Δ′ less-step₈)
less-checkpoint₉ = less-step-term₉

less-checkpoint₁₀ : Term (Step.Δ′ less-step₁₀)
less-checkpoint₁₀ = less-step-term₁₁

less-checkpoint₁₁ : Term (Step.Δ′ less-step₁₁)
less-checkpoint₁₁ = less-step-term₁₂

less-checkpoint₁₂ : Term (Step.Δ′ less-step₁₂)
less-checkpoint₁₂ = less-step-term₁₃

less-checkpoint₁₃ : Term (Step.Δ′ less-step₁₃)
less-checkpoint₁₃ = less-step-term₁₄

more-checkpoint₀↠₁ :
  more-checkpoint₀ —↠[ keep ∷ [] ] more-checkpoint₁
more-checkpoint₀↠₁ =
  more-checkpoint₀
  —→[ keep ]⟨ Step.reduction more-step₀ ⟩
  more-checkpoint₁ ∎[]

less-checkpoint₀↠₁ :
  less-checkpoint₀ —↠[ bind ★ ∷ bind (＇ Fin.zero) ∷ keep ∷ [] ] less-checkpoint₁
less-checkpoint₀↠₁ =
  less-checkpoint₀
  —→[ bind ★ ]⟨ Step.reduction less-step₀ ⟩
  less-step-term₁
  —→[ bind (＇ Fin.zero) ]⟨ Step.reduction less-step₁ ⟩
  less-step-term₂
  —→[ keep ]⟨ Step.reduction less-step₂ ⟩
  less-checkpoint₁
  ∎[]

more-checkpoint₁↠₂ :
  more-checkpoint₁ —↠[ keep ∷ [] ] more-checkpoint₂
more-checkpoint₁↠₂ =
  more-checkpoint₁
  —→[ keep ]⟨ Step.reduction more-step₁ ⟩
  more-checkpoint₂ ∎[]

less-checkpoint₁↠₂ :
  less-checkpoint₁ —↠[ [] ] less-checkpoint₂
less-checkpoint₁↠₂ =
  less-checkpoint₂ ∎[]

more-checkpoint₂↠₃ :
  more-checkpoint₂ —↠[ bind (‵ `ℕ) ∷ [] ] more-checkpoint₃
more-checkpoint₂↠₃ =
  more-checkpoint₂
  —→[ bind (‵ `ℕ) ]⟨ Step.reduction more-step₂ ⟩
  more-checkpoint₃ ∎[]

less-checkpoint₂↠₃ :
  less-checkpoint₂ —↠[ [] ] less-checkpoint₃
less-checkpoint₂↠₃ =
  less-checkpoint₃ ∎[]

more-checkpoint₃↠₄ :
  more-checkpoint₃ —↠[ keep ∷ [] ] more-checkpoint₄
more-checkpoint₃↠₄ =
  more-checkpoint₃
  —→[ keep ]⟨ Step.reduction more-step₃ ⟩
  more-checkpoint₄ ∎[]

less-checkpoint₃↠₄ :
  less-checkpoint₃ —↠[ [] ] less-checkpoint₄
less-checkpoint₃↠₄ =
  less-checkpoint₄ ∎[]

more-checkpoint₄↠₅ :
  more-checkpoint₄ —↠[ keep ∷ [] ] more-checkpoint₅
more-checkpoint₄↠₅ =
  more-checkpoint₄
  —→[ keep ]⟨ Step.reduction more-step₄ ⟩
  more-checkpoint₅ ∎[]

less-checkpoint₄↠₅ :
  less-checkpoint₄ —↠[ keep ∷ [] ] less-checkpoint₅
less-checkpoint₄↠₅ =
  less-checkpoint₄
  —→[ keep ]⟨ Step.reduction less-step₃ ⟩
  less-checkpoint₅
  ∎[]

more-checkpoint₅↠₆ :
  more-checkpoint₅ —↠[ keep ∷ [] ] more-checkpoint₆
more-checkpoint₅↠₆ =
  more-checkpoint₅
  —→[ keep ]⟨ Step.reduction more-step₅ ⟩
  more-checkpoint₆ ∎[]

less-checkpoint₅↠₆ :
  less-checkpoint₅ —↠[ keep ∷ [] ] less-checkpoint₆
less-checkpoint₅↠₆ =
  less-checkpoint₅
  —→[ keep ]⟨ Step.reduction less-step₄ ⟩
  less-checkpoint₆
  ∎[]

more-checkpoint₆↠₇ :
  more-checkpoint₆ —↠[ keep ∷ [] ] more-checkpoint₇
more-checkpoint₆↠₇ =
  more-checkpoint₆
  —→[ keep ]⟨ Step.reduction more-step₆ ⟩
  more-checkpoint₇ ∎[]

less-checkpoint₆↠₇ :
  less-checkpoint₆ —↠[ keep ∷ [] ] less-checkpoint₇
less-checkpoint₆↠₇ =
  less-checkpoint₆
  —→[ keep ]⟨ Step.reduction less-step₅ ⟩
  less-checkpoint₇
  ∎[]

more-checkpoint₇↠₈ :
  more-checkpoint₇ —↠[ keep ∷ [] ] more-checkpoint₈
more-checkpoint₇↠₈ =
  more-checkpoint₇
  —→[ keep ]⟨ Step.reduction more-step₇ ⟩
  more-checkpoint₈ ∎[]

less-checkpoint₇↠₈ :
  less-checkpoint₇ —↠[ keep ∷ keep ∷ [] ] less-checkpoint₈
less-checkpoint₇↠₈ =
  less-checkpoint₇
  —→[ keep ]⟨ Step.reduction less-step₆ ⟩
  less-step-term₇
  —→[ keep ]⟨ Step.reduction less-step₇ ⟩
  less-checkpoint₈
  ∎[]

more-checkpoint₈↠₉ :
  more-checkpoint₈ —↠[ keep ∷ [] ] more-checkpoint₉
more-checkpoint₈↠₉ =
  more-checkpoint₈
  —→[ keep ]⟨ Step.reduction more-step₈ ⟩
  more-checkpoint₉ ∎[]

less-checkpoint₈↠₉ :
  less-checkpoint₈ —↠[ keep ∷ [] ] less-checkpoint₉
less-checkpoint₈↠₉ =
  less-checkpoint₈
  —→[ keep ]⟨ Step.reduction less-step₈ ⟩
  less-checkpoint₉
  ∎[]

more-checkpoint₉↠₁₀ :
  more-checkpoint₉ —↠[ keep ∷ [] ] more-checkpoint₁₀
more-checkpoint₉↠₁₀ =
  more-checkpoint₉
  —→[ keep ]⟨ Step.reduction more-step₉ ⟩
  more-checkpoint₁₀ ∎[]

less-checkpoint₉↠₁₀ :
  less-checkpoint₉ —↠[ keep ∷ keep ∷ [] ] less-checkpoint₁₀
less-checkpoint₉↠₁₀ =
  less-checkpoint₉
  —→[ keep ]⟨ Step.reduction less-step₉ ⟩
  less-step-term₁₀
  —→[ keep ]⟨ Step.reduction less-step₁₀ ⟩
  less-checkpoint₁₀
  ∎[]

more-checkpoint₁₀↠₁₁ :
  more-checkpoint₁₀ —↠[ keep ∷ [] ] more-checkpoint₁₁
more-checkpoint₁₀↠₁₁ =
  more-checkpoint₁₀
  —→[ keep ]⟨ Step.reduction more-step₁₀ ⟩
  more-checkpoint₁₁ ∎[]

less-checkpoint₁₀↠₁₁ :
  less-checkpoint₁₀ —↠[ keep ∷ [] ] less-checkpoint₁₁
less-checkpoint₁₀↠₁₁ =
  less-checkpoint₁₀
  —→[ keep ]⟨ Step.reduction less-step₁₁ ⟩
  less-checkpoint₁₁
  ∎[]

more-checkpoint₁₁↠₁₂ :
  more-checkpoint₁₁ —↠[ keep ∷ [] ] more-checkpoint₁₂
more-checkpoint₁₁↠₁₂ =
  more-checkpoint₁₁
  —→[ keep ]⟨ Step.reduction more-step₁₁ ⟩
  more-checkpoint₁₂ ∎[]

less-checkpoint₁₁↠₁₂ :
  less-checkpoint₁₁ —↠[ keep ∷ [] ] less-checkpoint₁₂
less-checkpoint₁₁↠₁₂ =
  less-checkpoint₁₁
  —→[ keep ]⟨ Step.reduction less-step₁₂ ⟩
  less-checkpoint₁₂
  ∎[]

more-checkpoint₁₂↠₁₃ :
  more-checkpoint₁₂ —↠[ keep ∷ [] ] more-checkpoint₁₃
more-checkpoint₁₂↠₁₃ =
  more-checkpoint₁₂
  —→[ keep ]⟨ Step.reduction more-step₁₂ ⟩
  more-checkpoint₁₃ ∎[]

less-checkpoint₁₂↠₁₃ :
  less-checkpoint₁₂ —↠[ keep ∷ [] ] less-checkpoint₁₃
less-checkpoint₁₂↠₁₃ =
  less-checkpoint₁₂
  —→[ keep ]⟨ Step.reduction less-step₁₃ ⟩
  less-checkpoint₁₃
  ∎[]

more-final : more-checkpoint₁₃ ≡ C.blame
more-final = refl

less-final : less-checkpoint₁₃ ≡ C.blame
less-final = refl


------------------------------------------------------------------------
-- Initial cast-term imprecision
------------------------------------------------------------------------

checkpoint₀-imprecision :
  emptyᶜ CTI.⊢² more-checkpoint₀ ⊑ less-checkpoint₀ ∶ I.ι⊑ι
checkpoint₀-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (symᶜ nat-consistent-star)
      (symᶜ nat-consistent-star)
      (CTI.·⊑·²
        (CTI.•⊑²
          ∀X⇒★⊑★⇒★
          (CTI.·⊑·²
            (CTI.ƛ⊑ƛ²
              (CTI.x⊑x² {p = ∀X⇒★⊑★⇒★} Z Z))
            (CTI.cast⊑cast²
              (symᶜ ∀X⇒★∼∀X⇒★)
              (symᶜ ★⇒★∼∀X⇒★)
              (CTI.Λ⊑Λ²
                (C.ƛ ((C.ƛ (C.` 0)) C.·
                  (C.` 0 C.⟨ symᶜ star-consistent-X ⟩)))
                (C.ƛ ((C.ƛ (C.` 0)) C.·
                  (C.` 0 C.⟨ symᶜ star-consistent-X ⟩)))
                (CTI.ƛ⊑ƛ² {pA = I.X⊑X} {pB = I.★⊑★}
                  (CTI.·⊑·²
                    (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
                      (CTI.x⊑x² {p = I.★⊑★} Z Z))
                    (CTI.cast⊑cast²
                      (symᶜ star-consistent-X)
                      (symᶜ star-consistent-X)
                      (CTI.x⊑x² {p = I.X⊑X} Z Z)
                      I.★⊑★)))
                ∀X⇒★⊑∀X⇒★)
              ∀X⇒★⊑★⇒★))
          I.ι⊑★
          ℕ⇒★⊑★⇒★)
        (CTI.cast⊑cast²
          (symᶜ (id (‵ `ℕ)))
          (symᶜ (symᶜ nat-consistent-star))
          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
          I.ι⊑★))
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₀-ladder : String
checkpoint₀-ladder = impLadderDefault checkpoint₀-imprecision

checkpoint₀-ladder-pinned :
  checkpoint₀-ladder ≡
    "⟨⟩\n" ++
    "source term                      A                        ηᴸA                      ⊑ costs                                         ηᴿB                  B                    target term\n" ++
    "───────────────────────────────  ───────────────────────  ───────────────────────  ──────────────────────────────────────────────  ───────────────────  ───────────────────  ─────────────────────────────\n" ++
    "□₁ · □₂                          ℕ                        ℕ                        ℕ⊑ℕ                                             ℕ                    ℕ                    □₁ · □₂\n" ++
    "├ λx. □                          (ℕ ⇒ ℕ)                  (ℕ ⇒ ℕ)                  ℕ⊑ℕ, ℕ⊑ℕ                                        (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)              ├ λx. □\n" ++
    "│ x                              ℕ                        ℕ                        ℕ⊑ℕ                                             ℕ                    ℕ                    │ x\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                      ℕ                        ℕ                        ℕ⊑ℕ                                             ℕ                    ℕ                    └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                        ★                        ★                        ★⊑★                                             ★                    ★                      □₁ · □₂\n" ++
    "  ├ □ [ ℕ ]                      (ℕ ⇒ ★)                  (ℕ ⇒ ★)                  ι⊑★, ★⊑★                                        (★ ⇒ ★)              (★ ⇒ ★)                ├ ─\n" ++
    "  │ □₁ · □₂                      ∀ (X ⇒ ★)                ∀ (X ⇒ ★)                ∀⊑(mark X⊑★ at X, ★⊑★)                          (★ ⇒ ★)              (★ ⇒ ★)                │ □₁ · □₂\n" ++
    "  │ ├ λx. □                      (∀ (X ⇒ ★) ⇒ ∀ (X ⇒ ★))  (∀ (X ⇒ ★) ⇒ ∀ (X ⇒ ★))  ∀⊑(mark X⊑★ at X, ★⊑★), ∀⊑(mark X⊑★ at X, ★⊑★)  ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))    │ ├ λx. □\n" ++
    "  │ │ x                          ∀ (X ⇒ ★)                ∀ (X ⇒ ★)                ∀⊑(mark X⊑★ at X, ★⊑★)                          (★ ⇒ ★)              (★ ⇒ ★)                │ │ x\n" ++
    "  │ └ □ ⟨ ∀ (X ⇒ ★)↦∀ (X ⇒ ★) ⟩  ∀ (X ⇒ ★)                ∀ (X ⇒ ★)                ∀⊑(mark X⊑★ at X, ★⊑★)                          (★ ⇒ ★)              (★ ⇒ ★)                │ └ □ ⟨ ∀ (X ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │   Λ□                         ∀ (X ⇒ ★)                ∀ (X ⇒ ★)                ∀(X ≈ X, ★⊑★)                                   ∀ (X ⇒ ★)            ∀ (X ⇒ ★)              │   Λ□\n" ++
    "  │   λx. □                      (X ⇒ ★)                  (X ⇒ ★)                  X ≈ X, ★⊑★                                      (X ⇒ ★)              (X ⇒ ★)                │   λx. □\n" ++
    "  │   □₁ · □₂                    ★                        ★                        ★⊑★                                             ★                    ★                      │   □₁ · □₂\n" ++
    "  │   ├ λy. □                    (★ ⇒ ★)                  (★ ⇒ ★)                  ★⊑★, ★⊑★                                        (★ ⇒ ★)              (★ ⇒ ★)                │   ├ λy. □\n" ++
    "  │   │ y                        ★                        ★                        ★⊑★                                             ★                    ★                      │   │ y\n" ++
    "  │   └ □ ⟨ X↦★ ⟩                ★                        ★                        ★⊑★                                             ★                    ★                      │   └ □ ⟨ X↦★ ⟩\n" ++
    "  │     x                        X                        X                        X ≈ X                                           X                    X                      │     x\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩                    ℕ                        ℕ                        ι⊑★                                             ★                    ★                      └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                           ℕ                        ℕ                        ℕ⊑ℕ                                             ℕ                    ℕ                        42"
checkpoint₀-ladder-pinned = refl
------------------------------------------------------------------------
-- The two target allocations before the source allocation
------------------------------------------------------------------------

base-context : Ctx
base-context = ⟨ 0 , store-empty , [] ⟩

checkpoint₁-alpha-world : base-context ⊑ᶜ (base-context ,ˢ ★)
checkpoint₁-alpha-world = bindRightᶜ emptyᶜ ★ (inj₁ refl)

checkpoint₁-beta-fresh :
  RightBindFreshᶜ checkpoint₁-alpha-world (＇ Fin.zero)
checkpoint₁-beta-fresh =
  inj₂ (Fin.suc Fin.zero , refl , λ ())

checkpoint₁-world :
  base-context ⊑ᶜ ((base-context ,ˢ ★) ,ˢ ＇ Fin.zero)
checkpoint₁-world =
  bindRightᶜ checkpoint₁-alpha-world
    (＇ Fin.zero) checkpoint₁-beta-fresh

checkpoint₁-outside-world :
  ⇑ᵉᵗ base-context ⊑ᶜ ((base-context ,ˢ ★) ,ˢ ＇ Fin.zero)
checkpoint₁-outside-world = liftLeftᶜ checkpoint₁-world

checkpoint₁-alpha-ok :
  PivotUpdateᵗ
    (ηᴸᶜ checkpoint₁-outside-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₁-outside-world)
      (Fin.suc Fin.zero))
checkpoint₁-alpha-ok =
  repointⁱ (ηᴸᶜ checkpoint₁-outside-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₁-outside-world)
      (Fin.suc Fin.zero))
    (λ ())
    (λ { Fin.zero zero≠zero eq → zero≠zero refl })

checkpoint₁-alpha-representation :
  (＇ Fin.zero) ⊑ᵀ⟨ checkpoint₁-outside-world ⟩ ★
checkpoint₁-alpha-representation = I.X⊑★ refl

checkpoint₁-alpha-current :
  ⇑ᵉᵗ base-context ⊑ᶜ ((base-context ,ˢ ★) ,ˢ ＇ Fin.zero)
checkpoint₁-alpha-current =
  rebaseSourceᶜ checkpoint₁-outside-world Fin.zero
    (Fin.suc Fin.zero) checkpoint₁-alpha-ok
    open-frameᶜ
    checkpoint₁-alpha-representation

checkpoint₁-beta-ok :
  PivotUpdateᵗ
    (ηᴸᶜ checkpoint₁-alpha-current) Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₁-alpha-current) Fin.zero)
checkpoint₁-beta-ok =
  repointⁱ (ηᴸᶜ checkpoint₁-alpha-current) Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₁-alpha-current) Fin.zero)
    (λ ())
    (λ { Fin.zero zero≠zero eq → zero≠zero refl })

checkpoint₁-beta-representation :
  (＇ Fin.zero) ⊑ᵀ⟨ checkpoint₁-alpha-current ⟩
    (＇ (Fin.suc Fin.zero))
checkpoint₁-beta-representation = I.X⊑X

checkpoint₁-beta-current :
  ⇑ᵉᵗ base-context ⊑ᶜ ((base-context ,ˢ ★) ,ˢ ＇ Fin.zero)
checkpoint₁-beta-current =
  rebaseSourceᶜ checkpoint₁-alpha-current Fin.zero Fin.zero
    checkpoint₁-beta-ok open-frameᶜ checkpoint₁-beta-representation

checkpoint₁-beta-member :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    ∋ Fin.zero ⦂ ＇ (Fin.suc Fin.zero)
checkpoint₁-beta-member = Z∋ refl

checkpoint₁-alpha-member :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    ∋ Fin.suc Fin.zero ⦂ ★
checkpoint₁-alpha-member = S-bind∋ (Z∋ refl) refl

checkpoint₁-beta-reveal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↑[ Fin.zero ⦂ ＇ (Fin.suc Fin.zero) ]
      (seal Fin.zero (＇ (Fin.suc Fin.zero)) ↦↑ Conv.id↑ ★)
checkpoint₁-beta-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal checkpoint₁-beta-member)
    (Conv.⊢↑-id-star checkpoint₁-beta-member)

checkpoint₁-alpha-reveal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↑[ Fin.suc Fin.zero ⦂ ★ ]
      (seal (Fin.suc Fin.zero) ★ ↦↑ Conv.id↑ ★)
checkpoint₁-alpha-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal checkpoint₁-alpha-member)
    (Conv.⊢↑-id-star checkpoint₁-alpha-member)

checkpoint₁-beta-active :
  revealGeneratorPosition checkpoint₁-beta-reveal⊢
    ≢ generator-absent
checkpoint₁-beta-active ()

checkpoint₁-alpha-active :
  revealGeneratorPosition checkpoint₁-alpha-reveal⊢
    ≢ generator-absent
checkpoint₁-alpha-active ()


------------------------------------------------------------------------
-- Checkpoint 1: both target reveals are active
------------------------------------------------------------------------

checkpoint₁-source-X-to-star :
  idᶜ ⊢ Xᵗ {0} ∼ ★
checkpoint₁-source-X-to-star = symᶜ star-consistent-X

checkpoint₁-target-X-to-star :
  renameEnv∼ (Consistency.keep wk↪ᵗ) (idᶜ {Δ = 1})
    ⊢ Xᵗ {1} ∼ ★
checkpoint₁-target-X-to-star =
  renameᵐᶜ (Consistency.keep wk↪ᵗ) checkpoint₁-source-X-to-star

checkpoint₁-target-id-function :
  applyEnv (bind (＇ Fin.zero))
    (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})) ⊢
    dynamic-function ∼ dynamic-function
checkpoint₁-target-id-function =
  id {μ = flipᵐ (applyEnv (bind (＇ Fin.zero))
      (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})))} ★
  ↦
  id {μ = applyEnv (bind (＇ Fin.zero))
      (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))} ★

checkpoint₁-target-function : Term 2
checkpoint₁-target-function =
  C.ƛ ((C.ƛ (C.` 0)) C.·
    (C.` 0 C.⟨ checkpoint₁-target-X-to-star ⟩))

checkpoint₁-target-beta-reveal : Term 2
checkpoint₁-target-beta-reveal =
  checkpoint₁-target-function C.↑
    (seal Fin.zero (＇ (Fin.suc Fin.zero)) ↦↑ Conv.id↑ ★)

checkpoint₁-target-payload : Term 2
checkpoint₁-target-payload =
  checkpoint₁-target-beta-reveal C.↑
    (seal (Fin.suc Fin.zero) ★ ↦↑ Conv.id↑ ★)

checkpoint₁-target-function-⊢ :
  ((base-context ,ˢ ★) ,ˢ ＇ Fin.zero) ⊢
    checkpoint₁-target-function
    ⦂ ＇ Fin.zero ⇒ ★
checkpoint₁-target-function-⊢ =
  C.⊢ƛ
    (C.⊢·
      (C.⊢ƛ (C.⊢` Z))
      (C.⊢⟨⟩ (C.⊢` Z) checkpoint₁-target-X-to-star))

checkpoint₁-target-beta-reveal-⊢ :
  ((base-context ,ˢ ★) ,ˢ ＇ Fin.zero) ⊢
    checkpoint₁-target-beta-reveal
    ⦂ ＇ (Fin.suc Fin.zero) ⇒ ★
checkpoint₁-target-beta-reveal-⊢ =
  C.⊢reveal checkpoint₁-beta-reveal⊢ checkpoint₁-target-function-⊢

checkpoint₁-target-payload-⊢ :
  ((base-context ,ˢ ★) ,ˢ ＇ Fin.zero) ⊢
    checkpoint₁-target-payload
    ⦂ dynamic-function
checkpoint₁-target-payload-⊢ =
  C.⊢reveal checkpoint₁-alpha-reveal⊢
    checkpoint₁-target-beta-reveal-⊢

checkpoint₁-body-imprecision :
  bind-termᶜ checkpoint₁-beta-current I.X⊑X CTI.⊢²
    (C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-source-X-to-star ⟩)
    ⊑ (C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-target-X-to-star ⟩)
    ∶ I.★⊑★
checkpoint₁-body-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
      (CTI.x⊑x² {p = I.★⊑★} Z Z))
    (CTI.cast⊑cast²
      checkpoint₁-source-X-to-star
      checkpoint₁-target-X-to-star
      (CTI.x⊑x² {p = I.X⊑X} Z Z)
      I.★⊑★)

checkpoint₁-function-imprecision :
  checkpoint₁-beta-current CTI.⊢²
    C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-source-X-to-star ⟩))
    ⊑ C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-target-X-to-star ⟩))
    ∶ I.⇒⊑⇒ I.X⊑X I.★⊑★
checkpoint₁-function-imprecision =
  CTI.ƛ⊑ƛ² checkpoint₁-body-imprecision

checkpoint₁-reveals-imprecision :
  checkpoint₁-outside-world CTI.⊢²
    C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-source-X-to-star ⟩))
    ⊑ checkpoint₁-target-payload
    ∶ I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★
checkpoint₁-reveals-imprecision =
  CTI.⊑reveal-rebase²
    {M′ = checkpoint₁-target-beta-reveal}
    checkpoint₁-alpha-reveal⊢
    (source-rebase-now checkpoint₁-alpha-ok
      checkpoint₁-alpha-representation)
    (CTI.⊑reveal-rebase²
      {M′ = checkpoint₁-target-function}
      checkpoint₁-beta-reveal⊢
      (source-rebase-now checkpoint₁-beta-ok
        checkpoint₁-beta-representation)
      checkpoint₁-function-imprecision
      (I.⇒⊑⇒ I.X⊑X I.★⊑★))
    (I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★)

checkpoint₁-poly-imprecision :
  checkpoint₁-world CTI.⊢²
    C.Λ (C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-source-X-to-star ⟩)))
    ⊑ checkpoint₁-target-payload
    ∶ ∀X⇒★⊑★⇒★
checkpoint₁-poly-imprecision =
  CTI.Λ⊑²
    nonvar-fun X∈X⇒★
    (C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-source-X-to-star ⟩)))
    checkpoint₁-target-payload-⊢
    checkpoint₁-reveals-imprecision
    ∀X⇒★⊑★⇒★

checkpoint₁-imprecision :
  checkpoint₁-world CTI.⊢²
    more-checkpoint₁ ⊑ less-checkpoint₁ ∶ I.ι⊑ι
checkpoint₁-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (symᶜ nat-consistent-star)
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★) (symᶜ nat-consistent-star)))
      (CTI.·⊑·²
        (CTI.•⊑²
          ∀X⇒★⊑★⇒★
          (CTI.cast⊑cast²
            (symᶜ ∀X⇒★∼∀X⇒★)
            checkpoint₁-target-id-function
            checkpoint₁-poly-imprecision
            ∀X⇒★⊑★⇒★)
          I.ι⊑★
          ℕ⇒★⊑★⇒★)
        (CTI.cast⊑cast²
          (symᶜ (id (‵ `ℕ)))
          (id (‵ `ℕ) !)
          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
          I.ι⊑★))
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁-ladder : String
checkpoint₁-ladder = impLadderDefault checkpoint₁-imprecision

checkpoint₁-ladder-pinned :
  checkpoint₁-ladder ≡
    "⟨X: ─ ⊑[X⊑★] X′↦＇Y′ │ Y: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                    A          ηᴸA        ⊑ costs                             ηᴿB      B         target term\n" ++
    "─────────────────────────────  ─────────  ─────────  ──────────────────────────────────  ───────  ────────  ─────────────────────────\n" ++
    "□₁ · □₂                        ℕ          ℕ          ℕ⊑ℕ                                 ℕ        ℕ         □₁ · □₂\n" ++
    "├ λx. □                        (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ℕ⊑ℕ, ℕ⊑ℕ                            (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λx. □\n" ++
    "│ x                            ℕ          ℕ          ℕ⊑ℕ                                 ℕ        ℕ         │ x\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                    ℕ          ℕ          ℕ⊑ℕ                                 ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                      ★          ★          ★⊑★                                 ★        ★           □₁ · □₂\n" ++
    "  ├ □ [ ℕ ]                    (ℕ ⇒ ★)    (ℕ ⇒ ★)    ι⊑★, ★⊑★                            (★ ⇒ ★)  (★ ⇒ ★)     ├ ─\n" ++
    "  │ □ ⟨ ∀ (Z ⇒ ★)↦∀ (Z ⇒ ★) ⟩  ∀ (Z ⇒ ★)  ∀ (Z ⇒ ★)  ∀⊑(mark X⊑★ at Z, ★⊑★)              (★ ⇒ ★)  (★ ⇒ ★)     │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ Λ□                         ∀ (Z ⇒ ★)  ∀ (Z ⇒ ★)  ∀⊑(mark X⊑★ at Z, ★⊑★)              (★ ⇒ ★)  (★ ⇒ ★)     │ ─\n" ++
    "  │ ─                          (Z ⇒ ★)    (Z ⇒ ★)    mark X⊑★ at Z, ★⊑★ + source rebase  (★ ⇒ ★)  (★ ⇒ ★)     │ □ ↑ ⇒-rev\n" ++
    "  │ ─                          (Z ⇒ ★)    (Y ⇒ ★)    Y ≈ Y, ★⊑★ + source rebase          (Y ⇒ ★)  (Y′ ⇒ ★)    │ □ ↑ ⇒-rev\n" ++
    "  │ λx. □                      (Z ⇒ ★)    (X ⇒ ★)    X ≈ X, ★⊑★                          (X ⇒ ★)  (X′ ⇒ ★)    │ λx. □\n" ++
    "  │ □₁ · □₂                    ★          ★          ★⊑★                                 ★        ★           │ □₁ · □₂\n" ++
    "  │ ├ λy. □                    (★ ⇒ ★)    (★ ⇒ ★)    ★⊑★, ★⊑★                            (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λy. □\n" ++
    "  │ │ y                        ★          ★          ★⊑★                                 ★        ★           │ │ y\n" ++
    "  │ └ □ ⟨ Z↦★ ⟩                ★          ★          ★⊑★                                 ★        ★           │ └ □ ⟨ X′↦★ ⟩\n" ++
    "  │   x                        Z          X          X ≈ X                               X        X′          │   x\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩                  ℕ          ℕ          ι⊑★                                 ★        ★           └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                         ℕ          ℕ          ℕ⊑ℕ                                 ℕ        ℕ             42"
checkpoint₁-ladder-pinned = refl
------------------------------------------------------------------------
-- Checkpoint 2: the source universal identity cast has distributed
------------------------------------------------------------------------

checkpoint₂-imprecision :
  checkpoint₁-world CTI.⊢²
    more-checkpoint₂ ⊑ less-checkpoint₂ ∶ I.ι⊑ι
checkpoint₂-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (symᶜ nat-consistent-star)
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★) (symᶜ nat-consistent-star)))
      (CTI.·⊑·²
        (CTI.cast⊑cast²
          (id (‵ `ℕ) ↦ id ★)
          checkpoint₁-target-id-function
          (CTI.•⊑²
            ∀X⇒★⊑★⇒★
            checkpoint₁-poly-imprecision
            I.ι⊑★
            ℕ⇒★⊑★⇒★)
          ℕ⇒★⊑★⇒★)
        (CTI.cast⊑cast²
          (symᶜ (id (‵ `ℕ)))
          (id (‵ `ℕ) !)
          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
          I.ι⊑★))
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₂-ladder : String
checkpoint₂-ladder = impLadderDefault checkpoint₂-imprecision

checkpoint₂-ladder-pinned :
  checkpoint₂-ladder ≡
    "⟨X: ─ ⊑[X⊑★] X′↦＇Y′ │ Y: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                A          ηᴸA        ⊑ costs                             ηᴿB      B         target term\n" ++
    "─────────────────────────  ─────────  ─────────  ──────────────────────────────────  ───────  ────────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ          ℕ          ℕ⊑ℕ                                 ℕ        ℕ         □₁ · □₂\n" ++
    "├ λx. □                    (ℕ ⇒ ℕ)    (ℕ ⇒ ℕ)    ℕ⊑ℕ, ℕ⊑ℕ                            (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λx. □\n" ++
    "│ x                        ℕ          ℕ          ℕ⊑ℕ                                 ℕ        ℕ         │ x\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ          ℕ          ℕ⊑ℕ                                 ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                  ★          ★          ★⊑★                                 ★        ★           □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)    (ℕ ⇒ ★)    ι⊑★, ★⊑★                            (★ ⇒ ★)  (★ ⇒ ★)     ├ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ [ ℕ ]                (ℕ ⇒ ★)    (ℕ ⇒ ★)    ι⊑★, ★⊑★                            (★ ⇒ ★)  (★ ⇒ ★)     │ ─\n" ++
    "  │ Λ□                     ∀ (Z ⇒ ★)  ∀ (Z ⇒ ★)  ∀⊑(mark X⊑★ at Z, ★⊑★)              (★ ⇒ ★)  (★ ⇒ ★)     │ ─\n" ++
    "  │ ─                      (Z ⇒ ★)    (Z ⇒ ★)    mark X⊑★ at Z, ★⊑★ + source rebase  (★ ⇒ ★)  (★ ⇒ ★)     │ □ ↑ ⇒-rev\n" ++
    "  │ ─                      (Z ⇒ ★)    (Y ⇒ ★)    Y ≈ Y, ★⊑★ + source rebase          (Y ⇒ ★)  (Y′ ⇒ ★)    │ □ ↑ ⇒-rev\n" ++
    "  │ λx. □                  (Z ⇒ ★)    (X ⇒ ★)    X ≈ X, ★⊑★                          (X ⇒ ★)  (X′ ⇒ ★)    │ λx. □\n" ++
    "  │ □₁ · □₂                ★          ★          ★⊑★                                 ★        ★           │ □₁ · □₂\n" ++
    "  │ ├ λy. □                (★ ⇒ ★)    (★ ⇒ ★)    ★⊑★, ★⊑★                            (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λy. □\n" ++
    "  │ │ y                    ★          ★          ★⊑★                                 ★        ★           │ │ y\n" ++
    "  │ └ □ ⟨ Z↦★ ⟩            ★          ★          ★⊑★                                 ★        ★           │ └ □ ⟨ X′↦★ ⟩\n" ++
    "  │   x                    Z          X          X ≈ X                               X        X′          │   x\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩              ℕ          ℕ          ι⊑★                                 ★        ★           └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ          ℕ          ℕ⊑ℕ                                 ℕ        ℕ             42"
checkpoint₂-ladder-pinned = refl
------------------------------------------------------------------------
-- Checkpoint 3: source allocation aligns with target alpha
------------------------------------------------------------------------

checkpoint₃-allocation-world :
  (base-context ,ˢ ℕᵗ) ⊑ᶜ ((base-context ,ˢ ★) ,ˢ ＇ Fin.zero)
checkpoint₃-allocation-world = bindLeftᶜ checkpoint₁-world ℕᵗ

checkpoint₃-alpha-ok :
  PivotUpdateᵗ
    (ηᴸᶜ checkpoint₃-allocation-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₃-allocation-world)
      (Fin.suc Fin.zero))
checkpoint₃-alpha-ok =
  repointⁱ (ηᴸᶜ checkpoint₃-allocation-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₃-allocation-world)
      (Fin.suc Fin.zero))
    (λ ())
    (λ { Fin.zero zero≠zero eq → zero≠zero refl })

checkpoint₃-alpha-representation :
  (＇ Fin.zero) ⊑ᵀ⟨ checkpoint₃-allocation-world ⟩ ★
checkpoint₃-alpha-representation = I.X⊑★ refl

checkpoint₃-world :
  (base-context ,ˢ ℕᵗ) ⊑ᶜ ((base-context ,ˢ ★) ,ˢ ＇ Fin.zero)
checkpoint₃-world =
  rebaseSourceᶜ checkpoint₃-allocation-world Fin.zero
    (Fin.suc Fin.zero) checkpoint₃-alpha-ok
    open-frameᶜ
    checkpoint₃-alpha-representation

checkpoint₃-beta-ok :
  PivotUpdateᵗ
    (ηᴸᶜ checkpoint₃-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₃-world) Fin.zero)
checkpoint₃-beta-ok =
  repointⁱ (ηᴸᶜ checkpoint₃-world) Fin.zero
    (toRenameⁱ (ηᴿᶜ checkpoint₃-world) Fin.zero)
    (λ ())
    (λ { Fin.zero zero≠zero eq → zero≠zero refl })

checkpoint₃-beta-representation :
  (＇ Fin.zero) ⊑ᵀ⟨ checkpoint₃-world ⟩
    (＇ (Fin.suc Fin.zero))
checkpoint₃-beta-representation = I.X⊑X

checkpoint₃-beta-current :
  (base-context ,ˢ ℕᵗ) ⊑ᶜ ((base-context ,ˢ ★) ,ˢ ＇ Fin.zero)
checkpoint₃-beta-current =
  rebaseSourceᶜ checkpoint₃-world Fin.zero Fin.zero
    checkpoint₃-beta-ok open-frameᶜ checkpoint₃-beta-representation

checkpoint₃-source-member :
  store-bind store-empty ℕᵗ ∋ Fin.zero ⦂ ℕᵗ
checkpoint₃-source-member = Z∋ refl

checkpoint₃-source-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    (seal Fin.zero ℕᵗ ↦↑ Conv.id↑ ★)
checkpoint₃-source-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal checkpoint₃-source-member)
    (Conv.⊢↑-id-star checkpoint₃-source-member)

checkpoint₃-source-active :
  revealGeneratorPosition checkpoint₃-source-reveal⊢
    ≢ generator-absent
checkpoint₃-source-active ()

checkpoint₃-source-id-argument :
  flipᵐ (extᵐ (λ (_ : TyVar 0) → ★∼X∼★)) ⊢ ℕᵗ ∼ ℕᵗ
checkpoint₃-source-id-argument = id (‵ `ℕ)

checkpoint₃-source-id-result :
  extᵐ (λ (_ : TyVar 0) → ★∼X∼★) ⊢ ★ ∼ ★
checkpoint₃-source-id-result = id ★

checkpoint₃-source-id-function :
  extᵐ (idᶜ {Δ = 0}) ⊢
    (ℕᵗ ⇒ ★) ∼ (ℕᵗ ⇒ ★)
checkpoint₃-source-id-function =
  id {μ = flipᵐ (extᵐ (idᶜ {Δ = 0}))} (‵ `ℕ)
  ↦
  id {μ = extᵐ (idᶜ {Δ = 0})} ★

checkpoint₃-target-id-argument :
  flipᵐ (applyEnv (bind (＇ Fin.zero))
    (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))) ⊢ ★ ∼ ★
checkpoint₃-target-id-argument = id ★

checkpoint₃-target-id-result :
  applyEnv (bind (＇ Fin.zero))
    (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})) ⊢ ★ ∼ ★
checkpoint₃-target-id-result = id ★

checkpoint₃-target-nat-to-star :
  renameEnv∼ (Consistency.skip id↪ᵗ)
    (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})) ⊢ ℕᵗ ∼ ★
checkpoint₃-target-nat-to-star = id (‵ `ℕ) !

checkpoint₃-body-imprecision :
  bind-termᶜ checkpoint₃-beta-current I.X⊑X CTI.⊢²
    (C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-source-X-to-star ⟩)
    ⊑ (C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-target-X-to-star ⟩)
    ∶ I.★⊑★
checkpoint₃-body-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
      (CTI.x⊑x² {p = I.★⊑★} Z Z))
    (CTI.cast⊑cast²
      checkpoint₁-source-X-to-star
      checkpoint₁-target-X-to-star
      (CTI.x⊑x² {p = I.X⊑X} Z Z)
      I.★⊑★)

checkpoint₃-function-imprecision :
  checkpoint₃-beta-current CTI.⊢²
    C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-source-X-to-star ⟩))
    ⊑ checkpoint₁-target-function
    ∶ I.⇒⊑⇒ I.X⊑X I.★⊑★
checkpoint₃-function-imprecision =
  CTI.ƛ⊑ƛ² checkpoint₃-body-imprecision

checkpoint₃-beta-imprecision :
  checkpoint₃-world CTI.⊢²
    C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-source-X-to-star ⟩))
    ⊑ checkpoint₁-target-beta-reveal
    ∶ I.⇒⊑⇒ I.X⊑X I.★⊑★
checkpoint₃-beta-imprecision =
  CTI.⊑reveal-rebase²
    {M′ = checkpoint₁-target-function}
    checkpoint₁-beta-reveal⊢
    (source-rebase-now checkpoint₃-beta-ok
      checkpoint₃-beta-representation)
    checkpoint₃-function-imprecision
    (I.⇒⊑⇒ I.X⊑X I.★⊑★)

checkpoint₃-reveals-imprecision :
  checkpoint₃-world CTI.⊢²
    (C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-source-X-to-star ⟩))) C.↑
      (seal Fin.zero ℕᵗ ↦↑ Conv.id↑ ★)
    ⊑ checkpoint₁-target-payload
    ∶ ℕ⇒★⊑★⇒★
checkpoint₃-reveals-imprecision =
  CTI.reveal⊑reveal²
    checkpoint₃-source-reveal⊢
    checkpoint₁-alpha-reveal⊢
    refl
    refl
    I.ι⊑★
    checkpoint₃-beta-imprecision
    ℕ⇒★⊑★⇒★

more-checkpoint₃-shape :
  more-checkpoint₃ ≡
    (C.ƛ (C.` 0)) C.·
      (((((C.ƛ ((C.ƛ (C.` 0)) C.·
          (C.` 0 C.⟨ checkpoint₁-source-X-to-star ⟩))) C.↑
          (seal Fin.zero ℕᵗ ↦↑ Conv.id↑ ★)) C.⟨
          checkpoint₃-source-id-function ⟩) C.·
        (C.$ (κℕ 42) C.⟨
          renameᵐᶜ (Consistency.skip id↪ᵗ)
            (symᶜ (id (‵ `ℕ))) ⟩)) C.⟨
        applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star) ⟩)
more-checkpoint₃-shape = refl

checkpoint₃-imprecision :
  checkpoint₃-world CTI.⊢²
    more-checkpoint₃ ⊑ less-checkpoint₃ ∶ I.ι⊑ι
checkpoint₃-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★) (symᶜ nat-consistent-star)))
      (CTI.·⊑·²
        (CTI.cast⊑cast²
          checkpoint₃-source-id-function
          checkpoint₁-target-id-function
          checkpoint₃-reveals-imprecision
          ℕ⇒★⊑★⇒★)
        (CTI.cast⊑cast²
          (renameᵐᶜ (Consistency.skip id↪ᵗ)
            (symᶜ (id (‵ `ℕ))))
          (id (‵ `ℕ) !)
          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
          I.ι⊑★))
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₃-ladder : String
checkpoint₃-ladder = impLadderDefault checkpoint₃-imprecision

checkpoint₃-ladder-pinned :
  checkpoint₃-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                            ηᴿB      B         target term\n" ++
    "─────────────────────────  ───────  ───────  ─────────────────────────────────  ───────  ────────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         □₁ · □₂\n" ++
    "├ λx. □                    (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                           (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λx. □\n" ++
    "│ x                        ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         │ x\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                                ★        ★           □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)     ├ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ ↑ ⇒-rev              (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + matched reveal partner  (★ ⇒ ★)  (★ ⇒ ★)     │ □ ↑ ⇒-rev\n" ++
    "  │ ─                      (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + source rebase         (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↑ ⇒-rev\n" ++
    "  │ λx. □                  (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★                         (Y ⇒ ★)  (X′ ⇒ ★)    │ λx. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                                ★        ★           │ □₁ · □₂\n" ++
    "  │ ├ λy. □                (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λy. □\n" ++
    "  │ │ y                    ★        ★        ★⊑★                                ★        ★           │ │ y\n" ++
    "  │ └ □ ⟨ X↦★ ⟩            ★        ★        ★⊑★                                ★        ★           │ └ □ ⟨ X′↦★ ⟩\n" ++
    "  │   x                    X        Y        Y ≈ Y                              Y        X′          │   x\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩              ℕ        ℕ        ι⊑★                                ★        ★           └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ             42"
checkpoint₃-ladder-pinned = refl
------------------------------------------------------------------------
-- Checkpoints 4–6: ordinary identity casts distribute and erase
------------------------------------------------------------------------

checkpoint₄-imprecision :
  checkpoint₃-world CTI.⊢²
    more-checkpoint₄ ⊑ less-checkpoint₄ ∶ I.ι⊑ι
checkpoint₄-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★) (symᶜ nat-consistent-star)))
      (CTI.·⊑·²
        (CTI.cast⊑cast²
          checkpoint₃-source-id-function
          checkpoint₁-target-id-function
          checkpoint₃-reveals-imprecision
          ℕ⇒★⊑★⇒★)
        (CTI.⊑cast²
          (id (‵ `ℕ) !)
          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
          I.ι⊑★))
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₄-ladder : String
checkpoint₄-ladder = impLadderDefault checkpoint₄-imprecision

checkpoint₄-ladder-pinned :
  checkpoint₄-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                            ηᴿB      B         target term\n" ++
    "─────────────────────────  ───────  ───────  ─────────────────────────────────  ───────  ────────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         □₁ · □₂\n" ++
    "├ λx. □                    (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                           (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λx. □\n" ++
    "│ x                        ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         │ x\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                                ★        ★           □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)     ├ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ ↑ ⇒-rev              (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + matched reveal partner  (★ ⇒ ★)  (★ ⇒ ★)     │ □ ↑ ⇒-rev\n" ++
    "  │ ─                      (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + source rebase         (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↑ ⇒-rev\n" ++
    "  │ λx. □                  (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★                         (Y ⇒ ★)  (X′ ⇒ ★)    │ λx. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                                ★        ★           │ □₁ · □₂\n" ++
    "  │ ├ λy. □                (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λy. □\n" ++
    "  │ │ y                    ★        ★        ★⊑★                                ★        ★           │ │ y\n" ++
    "  │ └ □ ⟨ X↦★ ⟩            ★        ★        ★⊑★                                ★        ★           │ └ □ ⟨ X′↦★ ⟩\n" ++
    "  │   x                    X        Y        Y ≈ Y                              Y        X′          │   x\n" ++
    "  └ ─                      ℕ        ℕ        ι⊑★                                ★        ★           └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ             42"
checkpoint₄-ladder-pinned = refl
checkpoint₅-imprecision :
  checkpoint₃-world CTI.⊢²
    more-checkpoint₅ ⊑ less-checkpoint₅ ∶ I.ι⊑ι
checkpoint₅-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★) (symᶜ nat-consistent-star)))
      (CTI.cast⊑cast²
        checkpoint₃-source-id-result
        checkpoint₃-target-id-result
        (CTI.·⊑·²
          checkpoint₃-reveals-imprecision
          (CTI.cast⊑cast²
            checkpoint₃-source-id-argument
            checkpoint₃-target-id-argument
            (CTI.⊑cast²
              (id (‵ `ℕ) !)
              (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
              I.ι⊑★)
            I.ι⊑★))
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₅-ladder : String
checkpoint₅-ladder = impLadderDefault checkpoint₅-imprecision

checkpoint₅-ladder-pinned :
  checkpoint₅-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term      A        ηᴸA      ⊑ costs                            ηᴿB      B         target term\n" ++
    "───────────────  ───────  ───────  ─────────────────────────────────  ───────  ────────  ────────────────\n" ++
    "□₁ · □₂          ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         □₁ · □₂\n" ++
    "├ λx. □          (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                           (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λx. □\n" ++
    "│ x              ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         │ x\n" ++
    "└ □ ⟨ ★↦ℕ ⟩      ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩      ★        ★        ★⊑★                                ★        ★           □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂        ★        ★        ★⊑★                                ★        ★           □₁ · □₂\n" ++
    "  ├ □ ↑ ⇒-rev    (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + matched reveal partner  (★ ⇒ ★)  (★ ⇒ ★)     ├ □ ↑ ⇒-rev\n" ++
    "  │ ─            (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + source rebase         (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↑ ⇒-rev\n" ++
    "  │ λx. □        (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★                         (Y ⇒ ★)  (X′ ⇒ ★)    │ λx. □\n" ++
    "  │ □₁ · □₂      ★        ★        ★⊑★                                ★        ★           │ □₁ · □₂\n" ++
    "  │ ├ λy. □      (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λy. □\n" ++
    "  │ │ y          ★        ★        ★⊑★                                ★        ★           │ │ y\n" ++
    "  │ └ □ ⟨ X↦★ ⟩  ★        ★        ★⊑★                                ★        ★           │ └ □ ⟨ X′↦★ ⟩\n" ++
    "  │   x          X        Y        Y ≈ Y                              Y        X′          │   x\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩    ℕ        ℕ        ι⊑★                                ★        ★           └ □ ⟨ ★↦★ ⟩\n" ++
    "    ─            ℕ        ℕ        ι⊑★                                ★        ★             □ ⟨ ℕ↦★ ⟩\n" ++
    "    42           ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ             42"
checkpoint₅-ladder-pinned = refl
checkpoint₆-imprecision :
  checkpoint₃-world CTI.⊢²
    more-checkpoint₆ ⊑ less-checkpoint₆ ∶ I.ι⊑ι
checkpoint₆-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★) (symᶜ nat-consistent-star)))
      (CTI.cast⊑cast²
        checkpoint₃-source-id-result
        checkpoint₃-target-id-result
        (CTI.·⊑·²
          checkpoint₃-reveals-imprecision
          (CTI.⊑cast²
            (id (‵ `ℕ) !)
            (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
            I.ι⊑★))
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₆-ladder : String
checkpoint₆-ladder = impLadderDefault checkpoint₆-imprecision

checkpoint₆-ladder-pinned :
  checkpoint₆-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term      A        ηᴸA      ⊑ costs                            ηᴿB      B         target term\n" ++
    "───────────────  ───────  ───────  ─────────────────────────────────  ───────  ────────  ────────────────\n" ++
    "□₁ · □₂          ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         □₁ · □₂\n" ++
    "├ λx. □          (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                           (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λx. □\n" ++
    "│ x              ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         │ x\n" ++
    "└ □ ⟨ ★↦ℕ ⟩      ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩      ★        ★        ★⊑★                                ★        ★           □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂        ★        ★        ★⊑★                                ★        ★           □₁ · □₂\n" ++
    "  ├ □ ↑ ⇒-rev    (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + matched reveal partner  (★ ⇒ ★)  (★ ⇒ ★)     ├ □ ↑ ⇒-rev\n" ++
    "  │ ─            (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + source rebase         (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↑ ⇒-rev\n" ++
    "  │ λx. □        (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★                         (Y ⇒ ★)  (X′ ⇒ ★)    │ λx. □\n" ++
    "  │ □₁ · □₂      ★        ★        ★⊑★                                ★        ★           │ □₁ · □₂\n" ++
    "  │ ├ λy. □      (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λy. □\n" ++
    "  │ │ y          ★        ★        ★⊑★                                ★        ★           │ │ y\n" ++
    "  │ └ □ ⟨ X↦★ ⟩  ★        ★        ★⊑★                                ★        ★           │ └ □ ⟨ X′↦★ ⟩\n" ++
    "  │   x          X        Y        Y ≈ Y                              Y        X′          │   x\n" ++
    "  └ ─            ℕ        ℕ        ι⊑★                                ★        ★           └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42           ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ             42"
checkpoint₆-ladder-pinned = refl
------------------------------------------------------------------------
-- Checkpoint 7: the alpha arrow reveal distributes
------------------------------------------------------------------------

checkpoint₇-source-conceal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↓[ Fin.zero ⦂ ℕᵗ ]
    Conv.seal Fin.zero ℕᵗ
checkpoint₇-source-conceal⊢ =
  Conv.⊢↓-seal checkpoint₃-source-member

checkpoint₇-alpha-conceal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↓[ Fin.suc Fin.zero ⦂ ★ ]
      Conv.seal (Fin.suc Fin.zero) ★
checkpoint₇-alpha-conceal⊢ =
  Conv.⊢↓-seal checkpoint₁-alpha-member

checkpoint₇-source-identity-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    Conv.id↑ ★
checkpoint₇-source-identity-reveal⊢ =
  Conv.⊢↑-id-star checkpoint₃-source-member

checkpoint₇-alpha-identity-reveal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↑[ Fin.suc Fin.zero ⦂ ★ ] Conv.id↑ ★
checkpoint₇-alpha-identity-reveal⊢ =
  Conv.⊢↑-id-star checkpoint₁-alpha-member

checkpoint₇-alpha-conceal-imprecision :
  checkpoint₃-world CTI.⊢²
    (C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ)
    ⊑ ((C.$ (κℕ 42) C.⟨ checkpoint₃-target-nat-to-star ⟩) C.↓
      Conv.seal (Fin.suc Fin.zero) ★)
    ∶ I.X⊑X
checkpoint₇-alpha-conceal-imprecision =
  CTI.conceal⊑conceal²
    checkpoint₇-source-conceal⊢
    checkpoint₇-alpha-conceal⊢
    refl
    refl
    I.ι⊑★
    (CTI.⊑cast²
      checkpoint₃-target-nat-to-star
      (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
      I.ι⊑★)
    I.X⊑X

checkpoint₇-application-imprecision :
  checkpoint₃-world CTI.⊢²
    (C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-source-X-to-star ⟩))) C.·
      (C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ)
    ⊑ checkpoint₁-target-beta-reveal C.·
      ((C.$ (κℕ 42) C.⟨ checkpoint₃-target-nat-to-star ⟩) C.↓
        Conv.seal (Fin.suc Fin.zero) ★)
    ∶ I.★⊑★
checkpoint₇-application-imprecision =
  CTI.·⊑·²
    checkpoint₃-beta-imprecision
    checkpoint₇-alpha-conceal-imprecision

checkpoint₇-identity-reveals-imprecision :
  checkpoint₃-world CTI.⊢²
    ((C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-source-X-to-star ⟩))) C.·
      (C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ)) C.↑
      Conv.id↑ ★
    ⊑ (checkpoint₁-target-beta-reveal C.·
      ((C.$ (κℕ 42) C.⟨ checkpoint₃-target-nat-to-star ⟩) C.↓
        Conv.seal (Fin.suc Fin.zero) ★)) C.↑ Conv.id↑ ★
    ∶ I.★⊑★
checkpoint₇-identity-reveals-imprecision =
  CTI.reveal⊑reveal²
    checkpoint₇-source-identity-reveal⊢
    checkpoint₇-alpha-identity-reveal⊢
    refl
    refl
    I.ι⊑★
    checkpoint₇-application-imprecision
    I.★⊑★

checkpoint₇-imprecision :
  checkpoint₃-world CTI.⊢²
    more-checkpoint₇ ⊑ less-checkpoint₇ ∶ I.ι⊑ι
checkpoint₇-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★) (symᶜ nat-consistent-star)))
      (CTI.cast⊑cast²
        checkpoint₃-source-id-result
        checkpoint₃-target-id-result
        checkpoint₇-identity-reveals-imprecision
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₇-ladder : String
checkpoint₇-ladder = impLadderDefault checkpoint₇-imprecision

checkpoint₇-ladder-pinned :
  checkpoint₇-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term      A        ηᴸA      ⊑ costs                          ηᴿB      B         target term\n" ++
    "───────────────  ───────  ───────  ───────────────────────────────  ───────  ────────  ────────────────\n" ++
    "□₁ · □₂          ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ         □₁ · □₂\n" ++
    "├ λx. □          (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λx. □\n" ++
    "│ x              ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ         │ x\n" ++
    "└ □ ⟨ ★↦ℕ ⟩      ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩      ★        ★        ★⊑★                              ★        ★           □ ⟨ ★↦★ ⟩\n" ++
    "  □ ↑ id         ★        ★        ★⊑★ + matched reveal partner     ★        ★           □ ↑ id\n" ++
    "  □₁ · □₂        ★        ★        ★⊑★                              ★        ★           □₁ · □₂\n" ++
    "  ├ ─            (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + source rebase       (Z ⇒ ★)  (Y′ ⇒ ★)    ├ □ ↑ ⇒-rev\n" ++
    "  │ λx. □        (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★                       (Y ⇒ ★)  (X′ ⇒ ★)    │ λx. □\n" ++
    "  │ □₁ · □₂      ★        ★        ★⊑★                              ★        ★           │ □₁ · □₂\n" ++
    "  │ ├ λy. □      (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                         (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λy. □\n" ++
    "  │ │ y          ★        ★        ★⊑★                              ★        ★           │ │ y\n" ++
    "  │ └ □ ⟨ X↦★ ⟩  ★        ★        ★⊑★                              ★        ★           │ └ □ ⟨ X′↦★ ⟩\n" ++
    "  │   x          X        Y        Y ≈ Y                            Y        X′          │   x\n" ++
    "  └ □ ↓ seal X   X        Z        Z ≈ Z + matched conceal partner  Z        Y′          └ □ ↓ seal Y′\n" ++
    "    ─            ℕ        ℕ        ι⊑★                              ★        ★             □ ⟨ ℕ↦★ ⟩\n" ++
    "    42           ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ             42"
checkpoint₇-ladder-pinned = refl
------------------------------------------------------------------------
-- Checkpoints 8–9: target structural-identity reveals are forced
------------------------------------------------------------------------

checkpoint₈-beta-conceal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↓[ Fin.zero ⦂ ＇ (Fin.suc Fin.zero) ]
      Conv.seal Fin.zero (＇ (Fin.suc Fin.zero))
checkpoint₈-beta-conceal⊢ =
  Conv.⊢↓-seal checkpoint₁-beta-member

checkpoint₈-beta-conceal-active :
  concealGeneratorPosition checkpoint₈-beta-conceal⊢
    ≢ generator-absent
checkpoint₈-beta-conceal-active ()

checkpoint₈-beta-identity-reveal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↑[ Fin.zero ⦂ ＇ (Fin.suc Fin.zero) ] Conv.id↑ ★
checkpoint₈-beta-identity-reveal⊢ =
  Conv.⊢↑-id-star checkpoint₁-beta-member

checkpoint₈-source-identity-absent :
  revealGeneratorPosition checkpoint₇-source-identity-reveal⊢
    ≡ generator-absent
checkpoint₈-source-identity-absent = refl

checkpoint₈-beta-identity-absent :
  revealGeneratorPosition checkpoint₈-beta-identity-reveal⊢
    ≡ generator-absent
checkpoint₈-beta-identity-absent = refl

checkpoint₈-alpha-identity-absent :
  revealGeneratorPosition checkpoint₇-alpha-identity-reveal⊢
    ≡ generator-absent
checkpoint₈-alpha-identity-absent = refl

checkpoint₈-beta-conceal-imprecision :
  checkpoint₃-beta-current CTI.⊢²
    (C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ)
    ⊑ (((C.$ (κℕ 42) C.⟨ checkpoint₃-target-nat-to-star ⟩)
      C.↓ Conv.seal (Fin.suc Fin.zero) ★)
      C.↓ Conv.seal Fin.zero (＇ (Fin.suc Fin.zero)))
    ∶ I.X⊑X
checkpoint₈-beta-conceal-imprecision =
  CTI.⊑conceal-rebase²
    checkpoint₈-beta-conceal⊢
    (source-rebase-now checkpoint₃-beta-ok
      checkpoint₃-beta-representation)
    checkpoint₇-alpha-conceal-imprecision
    I.X⊑X

checkpoint₈-casted-argument-imprecision :
  checkpoint₃-beta-current CTI.⊢²
    ((C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ) C.⟨
      checkpoint₁-source-X-to-star ⟩)
    ⊑ ((((C.$ (κℕ 42) C.⟨ checkpoint₃-target-nat-to-star ⟩)
      C.↓ Conv.seal (Fin.suc Fin.zero) ★)
      C.↓ Conv.seal Fin.zero (＇ (Fin.suc Fin.zero))) C.⟨
      checkpoint₁-target-X-to-star ⟩)
    ∶ I.★⊑★
checkpoint₈-casted-argument-imprecision =
  CTI.cast⊑cast²
    checkpoint₁-source-X-to-star
    checkpoint₁-target-X-to-star
    checkpoint₈-beta-conceal-imprecision
    I.★⊑★

checkpoint₈-core-imprecision :
  checkpoint₃-beta-current CTI.⊢²
    (C.ƛ (C.` 0)) C.·
      ((C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ) C.⟨
        checkpoint₁-source-X-to-star ⟩)
    ⊑ (C.ƛ (C.` 0)) C.·
      ((((C.$ (κℕ 42) C.⟨ checkpoint₃-target-nat-to-star ⟩)
        C.↓ Conv.seal (Fin.suc Fin.zero) ★)
        C.↓ Conv.seal Fin.zero (＇ (Fin.suc Fin.zero))) C.⟨
        checkpoint₁-target-X-to-star ⟩)
    ∶ I.★⊑★
checkpoint₈-core-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
      (CTI.x⊑x² {p = I.★⊑★} Z Z))
    checkpoint₈-casted-argument-imprecision

checkpoint₈-identity-reveals-imprecision :
  checkpoint₃-beta-current CTI.⊢²
    (((C.ƛ (C.` 0)) C.·
      ((C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ) C.⟨
        checkpoint₁-source-X-to-star ⟩)) C.↑ Conv.id↑ ★)
    ⊑ ((((C.ƛ (C.` 0)) C.·
      ((((C.$ (κℕ 42) C.⟨ checkpoint₃-target-nat-to-star ⟩)
        C.↓ Conv.seal (Fin.suc Fin.zero) ★)
        C.↓ Conv.seal Fin.zero (＇ (Fin.suc Fin.zero))) C.⟨
        checkpoint₁-target-X-to-star ⟩)) C.↑ Conv.id↑ ★)
      C.↑ Conv.id↑ ★)
    ∶ I.★⊑★
checkpoint₈-identity-reveals-imprecision =
  CTI.⊑reveal-identity
    checkpoint₇-alpha-identity-reveal⊢
    checkpoint₈-alpha-identity-absent
    (CTI.⊑reveal-identity
      checkpoint₈-beta-identity-reveal⊢
      checkpoint₈-beta-identity-absent
      (CTI.reveal⊑-identity
        checkpoint₇-source-identity-reveal⊢
        checkpoint₈-source-identity-absent
        checkpoint₈-core-imprecision
        I.★⊑★)
      I.★⊑★)
    I.★⊑★

checkpoint₈-imprecision :
  checkpoint₃-beta-current CTI.⊢²
    more-checkpoint₈ ⊑ less-checkpoint₈ ∶ I.ι⊑ι
checkpoint₈-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★) (symᶜ nat-consistent-star)))
      (CTI.cast⊑cast²
        checkpoint₃-source-id-result
        checkpoint₃-target-id-result
        checkpoint₈-identity-reveals-imprecision
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₈-ladder : String
checkpoint₈-ladder = impLadderDefault checkpoint₈-imprecision

checkpoint₈-ladder-pinned :
  checkpoint₈-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: X↦ℕ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term     A        ηᴸA      ⊑ costs                          ηᴿB      B        target term\n" ++
    "──────────────  ───────  ───────  ───────────────────────────────  ───────  ───────  ───────────────\n" ++
    "□₁ · □₂         ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ        □₁ · □₂\n" ++
    "├ λx. □         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λx. □\n" ++
    "│ x             ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ        │ x\n" ++
    "└ □ ⟨ ★↦ℕ ⟩     ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩     ★        ★        ★⊑★                              ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─             ★        ★        ★⊑★ + generator absent           ★        ★          □ ↑ id\n" ++
    "  ─             ★        ★        ★⊑★ + generator absent           ★        ★          □ ↑ id\n" ++
    "  □ ↑ id        ★        ★        ★⊑★ + generator absent           ★        ★          ─\n" ++
    "  □₁ · □₂       ★        ★        ★⊑★                              ★        ★          □₁ · □₂\n" ++
    "  ├ λx. □       (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                         (★ ⇒ ★)  (★ ⇒ ★)    ├ λx. □\n" ++
    "  │ x           ★        ★        ★⊑★                              ★        ★          │ x\n" ++
    "  └ □ ⟨ X↦★ ⟩   ★        ★        ★⊑★                              ★        ★          └ □ ⟨ X′↦★ ⟩\n" ++
    "    ─           X        Y        Y ≈ Y + source rebase            Y        X′           □ ↓ seal X′\n" ++
    "    □ ↓ seal X  X        Z        Z ≈ Z + matched conceal partner  Z        Y′           □ ↓ seal Y′\n" ++
    "    ─           ℕ        ℕ        ι⊑★                              ★        ★            □ ⟨ ℕ↦★ ⟩\n" ++
    "    42          ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ            42"
checkpoint₈-ladder-pinned = refl
checkpoint₉-identity-reveals-imprecision :
  checkpoint₃-beta-current CTI.⊢²
    (((C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ) C.⟨
      checkpoint₁-source-X-to-star ⟩) C.↑ Conv.id↑ ★)
    ⊑ (((((C.$ (κℕ 42) C.⟨ checkpoint₃-target-nat-to-star ⟩)
      C.↓ Conv.seal (Fin.suc Fin.zero) ★)
      C.↓ Conv.seal Fin.zero (＇ (Fin.suc Fin.zero))) C.⟨
      checkpoint₁-target-X-to-star ⟩) C.↑ Conv.id↑ ★)
      C.↑ Conv.id↑ ★
    ∶ I.★⊑★
checkpoint₉-identity-reveals-imprecision =
  CTI.⊑reveal-identity
    checkpoint₇-alpha-identity-reveal⊢
    checkpoint₈-alpha-identity-absent
    (CTI.⊑reveal-identity
      checkpoint₈-beta-identity-reveal⊢
      checkpoint₈-beta-identity-absent
      (CTI.reveal⊑-identity
        checkpoint₇-source-identity-reveal⊢
        checkpoint₈-source-identity-absent
        checkpoint₈-casted-argument-imprecision
        I.★⊑★)
      I.★⊑★)
    I.★⊑★

checkpoint₉-imprecision :
  checkpoint₃-beta-current CTI.⊢²
    more-checkpoint₉ ⊑ less-checkpoint₉ ∶ I.ι⊑ι
checkpoint₉-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★) (symᶜ nat-consistent-star)))
      (CTI.cast⊑cast²
        checkpoint₃-source-id-result
        checkpoint₃-target-id-result
        checkpoint₉-identity-reveals-imprecision
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₉-ladder : String
checkpoint₉-ladder = impLadderDefault checkpoint₉-imprecision

checkpoint₉-ladder-pinned :
  checkpoint₉-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: X↦ℕ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term   A        ηᴸA      ⊑ costs                          ηᴿB      B        target term\n" ++
    "────────────  ───────  ───────  ───────────────────────────────  ───────  ───────  ─────────────\n" ++
    "□₁ · □₂       ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ        □₁ · □₂\n" ++
    "├ λx. □       (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λx. □\n" ++
    "│ x           ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ        │ x\n" ++
    "└ □ ⟨ ★↦ℕ ⟩   ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩   ★        ★        ★⊑★                              ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─           ★        ★        ★⊑★ + generator absent           ★        ★          □ ↑ id\n" ++
    "  ─           ★        ★        ★⊑★ + generator absent           ★        ★          □ ↑ id\n" ++
    "  □ ↑ id      ★        ★        ★⊑★ + generator absent           ★        ★          ─\n" ++
    "  □ ⟨ X↦★ ⟩   ★        ★        ★⊑★                              ★        ★          □ ⟨ X′↦★ ⟩\n" ++
    "  ─           X        Y        Y ≈ Y + source rebase            Y        X′         □ ↓ seal X′\n" ++
    "  □ ↓ seal X  X        Z        Z ≈ Z + matched conceal partner  Z        Y′         □ ↓ seal Y′\n" ++
    "  ─           ℕ        ℕ        ι⊑★                              ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42          ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ          42"
checkpoint₉-ladder-pinned = refl
------------------------------------------------------------------------
-- Checkpoints 10–13: identity erasure and common blame
------------------------------------------------------------------------

checkpoint₁₀-imprecision :
  checkpoint₃-beta-current CTI.⊢²
    more-checkpoint₁₀ ⊑ less-checkpoint₁₀ ∶ I.ι⊑ι
checkpoint₁₀-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★) (symᶜ nat-consistent-star)))
      (CTI.cast⊑cast²
        checkpoint₃-source-id-result
        checkpoint₃-target-id-result
        checkpoint₈-casted-argument-imprecision
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₀-ladder : String
checkpoint₁₀-ladder = impLadderDefault checkpoint₁₀-imprecision

checkpoint₁₀-ladder-pinned :
  checkpoint₁₀-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: X↦ℕ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term   A        ηᴸA      ⊑ costs                          ηᴿB      B        target term\n" ++
    "────────────  ───────  ───────  ───────────────────────────────  ───────  ───────  ─────────────\n" ++
    "□₁ · □₂       ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ        □₁ · □₂\n" ++
    "├ λx. □       (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λx. □\n" ++
    "│ x           ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ        │ x\n" ++
    "└ □ ⟨ ★↦ℕ ⟩   ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩   ★        ★        ★⊑★                              ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □ ⟨ X↦★ ⟩   ★        ★        ★⊑★                              ★        ★          □ ⟨ X′↦★ ⟩\n" ++
    "  ─           X        Y        Y ≈ Y + source rebase            Y        X′         □ ↓ seal X′\n" ++
    "  □ ↓ seal X  X        Z        Z ≈ Z + matched conceal partner  Z        Y′         □ ↓ seal Y′\n" ++
    "  ─           ℕ        ℕ        ι⊑★                              ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42          ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ          42"
checkpoint₁₀-ladder-pinned = refl
checkpoint₁₁-imprecision :
  checkpoint₃-beta-current CTI.⊢²
    more-checkpoint₁₁ ⊑ less-checkpoint₁₁ ∶ I.ι⊑ι
checkpoint₁₁-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★) (symᶜ nat-consistent-star)))
      checkpoint₈-casted-argument-imprecision
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₁-ladder : String
checkpoint₁₁-ladder = impLadderDefault checkpoint₁₁-imprecision

checkpoint₁₁-ladder-pinned :
  checkpoint₁₁-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: X↦ℕ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term   A        ηᴸA      ⊑ costs                          ηᴿB      B        target term\n" ++
    "────────────  ───────  ───────  ───────────────────────────────  ───────  ───────  ─────────────\n" ++
    "□₁ · □₂       ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ        □₁ · □₂\n" ++
    "├ λx. □       (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λx. □\n" ++
    "│ x           ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ        │ x\n" ++
    "└ □ ⟨ ★↦ℕ ⟩   ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ X↦★ ⟩   ★        ★        ★⊑★                              ★        ★          □ ⟨ X′↦★ ⟩\n" ++
    "  ─           X        Y        Y ≈ Y + source rebase            Y        X′         □ ↓ seal X′\n" ++
    "  □ ↓ seal X  X        Z        Z ≈ Z + matched conceal partner  Z        Y′         □ ↓ seal Y′\n" ++
    "  ─           ℕ        ℕ        ι⊑★                              ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42          ℕ        ℕ        ℕ⊑ℕ                              ℕ        ℕ          42"
checkpoint₁₁-ladder-pinned = refl
checkpoint₁₂-imprecision :
  checkpoint₃-beta-current CTI.⊢²
    more-checkpoint₁₂ ⊑ less-checkpoint₁₂ ∶ I.ι⊑ι
checkpoint₁₂-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.blame⊑² C.⊢blame (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₂-ladder : String
checkpoint₁₂-ladder = impLadderDefault checkpoint₁₂-imprecision

checkpoint₁₂-ladder-pinned :
  checkpoint₁₂-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: X↦ℕ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs   ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        □₁ · □₂\n" ++
    "├ λx. □      (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λx. □\n" ++
    "│ x          ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        │ x\n" ++
    "└ blame      ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        └ blame"
checkpoint₁₂-ladder-pinned = refl
checkpoint₁₃-imprecision :
  checkpoint₃-beta-current CTI.⊢²
    more-checkpoint₁₃ ⊑ less-checkpoint₁₃ ∶ I.ι⊑ι
checkpoint₁₃-imprecision =
  CTI.blame⊑² C.⊢blame (I.ι⊑ι {ι = `ℕ})

checkpoint₁₃-ladder : String
checkpoint₁₃-ladder = impLadderDefault checkpoint₁₃-imprecision

checkpoint₁₃-ladder-pinned :
  checkpoint₁₃-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: X↦ℕ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term\n" ++
    "───────────  ─  ───  ───────  ───  ─  ───────────\n" ++
    "blame        ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  blame"
checkpoint₁₃-ladder-pinned = refl
