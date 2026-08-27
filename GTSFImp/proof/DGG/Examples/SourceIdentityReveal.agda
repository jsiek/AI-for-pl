{-# OPTIONS --safe #-}

module proof.DGG.Examples.SourceIdentityReveal where

-- File Charter:
--   * Checks a source-only instantiation whose generated arrow reveal has an
--     active domain and a structural-identity result.
--   * Gives source typing and imprecision, ordinary compiler outputs, and one
--     simulation checkpoint after every source-side reduction.
--   * Exercises the source structural-identity reveal rule in a trusted
--     source-compiled execution.

import Data.Fin as Fin
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
import Data.Nat as Nat
open import Data.Product using (proj₁; proj₂)
open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TermCtx using (Z)
open import Consistency
open import GradualTerms renaming (_∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_)
import GradualTermImprecision as GTI
import Imprecision as I
open import TyStore using (TyStore; store-empty; store-bind; Z∋)
open import TyStore using (_∋_⦂_)
import Conversion as Conv
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
import CastTerms as C
open C using (Ctx; _,ˢ_)
open import Compile using (compile)
open import Primitives using (κℕ)
open import Reduction using
  (keep; bind; applyConsistency; []; _∷_; _—↠[_]_; _—→[_]⟨_⟩_;
   _—↠[_]⟨_⟩_; _∎[])
open import Eval using (step?)
import Example as Ex
import proof.DGG.OneStep as Step
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.World
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition; concealGeneratorPosition)
open import proof.DGG.ImpLadder using (impLadderDefault)

open GTI using () renaming
  (_∣_⊢ᴳ_⊑_⦂_⊑_∶_ to _∣_⊢ᴳ²_⊑_⦂_⊑_∶_)

------------------------------------------------------------------------
-- Source programs
------------------------------------------------------------------------

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

Xᵗ : ∀ {Δ} → Ty (Nat.suc Δ)
Xᵗ = ＇ Fin.zero

X⇒★ : ∀ {Δ} → Ty (Nat.suc Δ)
X⇒★ = Xᵗ ⇒ ★

∀X⇒★ : ∀ {Δ} → Ty Δ
∀X⇒★ = `∀ X⇒★

X∈X⇒★ : ∀ {Δ} → Fin.zero ∈ᵗ X⇒★ {Δ}
X∈X⇒★ = ∈-fun-left var-∈

ℓ-inner : Label
ℓ-inner = 0

ℓ-core : Label
ℓ-core = 1

ℓ-result : Label
ℓ-result = 2

more-precise : GTerm 0
more-precise =
  (ƛ ℕᵗ ⇒ ` 0) ·[ ℓ-result ]
    (((Λ
      (ƛ ＇ Fin.zero ⇒
        ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      `[ ℕᵗ ]) ·[ ℓ-core ] $ (κℕ 42))

less-precise : GTerm 0
less-precise =
  (ƛ ℕᵗ ⇒ ` 0) ·[ ℓ-result ]
    ((ƛ ★ ⇒
      ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
      ·[ ℓ-core ] $ (κℕ 42))


------------------------------------------------------------------------
-- Source typing and imprecision
------------------------------------------------------------------------

star-consistent-X : ∀ {Δ} → ★ ∼ Xᵗ {Δ}
star-consistent-X = total-from-★ (from★-★∼X∼★ refl)

nat-consistent-star : ∀ {Δ} → ℕᵗ {Δ} ∼ ★
nat-consistent-star = total-to-★ to★-ι

more-poly-⊢ :
  0 ∣ [] ⊢ᴳ
    Λ (ƛ ＇ Fin.zero ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
    ⦂ ∀X⇒★
more-poly-⊢ =
  ⊢Λ {zero∈A = X∈X⇒★}
    (ƛ ＇ Fin.zero ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
    (⊢ƛ
      (⊢·
        (⊢ƛ (⊢` Z))
        (⊢` Z)
        star-consistent-X))

less-function-⊢ :
  0 ∣ [] ⊢ᴳ
    (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
    ⦂ (★ ⇒ ★)
less-function-⊢ =
  ⊢ƛ
    (⊢·
      (⊢ƛ (⊢` Z))
      (⊢` Z)
      (id ★))

more-core-⊢ :
  0 ∣ [] ⊢ᴳ
    (((Λ
      (ƛ ＇ Fin.zero ⇒
        ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      `[ ℕᵗ ]) ·[ ℓ-core ] $ (κℕ 42)) ⦂ ★
more-core-⊢ =
  ⊢·
    (⊢• more-poly-⊢)
    (⊢$ (κℕ 42))
    (id (‵ `ℕ))

less-core-⊢ :
  0 ∣ [] ⊢ᴳ
    ((ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
      ·[ ℓ-core ] $ (κℕ 42)) ⦂ ★
less-core-⊢ =
  ⊢· less-function-⊢ (⊢$ (κℕ 42)) (？ (id (‵ `ℕ)))

more-precise-⊢ : 0 ∣ [] ⊢ᴳ more-precise ⦂ ℕᵗ
more-precise-⊢ =
  ⊢· (⊢ƛ (⊢` Z)) more-core-⊢ nat-consistent-star

less-precise-⊢ : 0 ∣ [] ⊢ᴳ less-precise ⦂ ℕᵗ
less-precise-⊢ =
  ⊢· (⊢ƛ (⊢` Z)) less-core-⊢ nat-consistent-star

X⇒★⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → I.instᵐ μ I.⊢ X⇒★ ⊑ (★ ⇒ ★)
X⇒★⊑★⇒★ = I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★

∀X⇒★⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ∀X⇒★ ⊑ (★ ⇒ ★)
∀X⇒★⊑★⇒★ = I.∀⊑ nonvar-fun X∈X⇒★ X⇒★⊑★⇒★

ℕ⇒★⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ (ℕᵗ ⇒ ★) ⊑ (★ ⇒ ★)
ℕ⇒★⊑★⇒★ = I.⇒⊑⇒ I.ι⊑★ I.★⊑★

body-imprecision :
  I.instᵐ (I.idᵐ {Δ = 0}) ∣
    (GTI.ctx-imp (＇ Fin.zero) ★ (I.X⊑★ refl) ∷ [])
    ⊢ᴳ²
      ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)
      ⊑ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)
      ⦂ ★ ⊑ ★ ∶ I.★⊑★
body-imprecision =
  GTI.·⊑·ᴳ
    (GTI.ƛ⊑ƛᴳ {pA = I.★⊑★} {pB = I.★⊑★}
      (GTI.x⊑xᴳ GTI.Zⁱ))
    (GTI.x⊑xᴳ GTI.Zⁱ)
    star-consistent-X
    (id ★)

function-imprecision :
  I.instᵐ (I.idᵐ {Δ = 0}) ∣ [] ⊢ᴳ²
    (ƛ ＇ Fin.zero ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
    ⊑ (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
    ⦂ X⇒★ ⊑ (★ ⇒ ★) ∶ X⇒★⊑★⇒★
function-imprecision =
  GTI.ƛ⊑ƛᴳ body-imprecision

poly-function-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ²
    Λ (ƛ ＇ Fin.zero ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
    ⊑ (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
    ⦂ ∀X⇒★ ⊑ (★ ⇒ ★) ∶ ∀X⇒★⊑★⇒★
poly-function-imprecision =
  GTI.Λ⊑ᴳ nonvar-fun X∈X⇒★ GTI.lift-[]
    (ƛ ＇ Fin.zero ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
    less-function-⊢
    function-imprecision

core-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ²
    (((Λ
      (ƛ ＇ Fin.zero ⇒
        ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      `[ ℕᵗ ]) ·[ ℓ-core ] $ (κℕ 42))
    ⊑ ((ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
      ·[ ℓ-core ] $ (κℕ 42))
    ⦂ ★ ⊑ ★ ∶ I.★⊑★
core-imprecision =
  GTI.·⊑·ᴳ
    (GTI.[]⊑ᴳ poly-function-imprecision I.ι⊑★ ℕ⇒★⊑★⇒★)
    (GTI.κ⊑κᴳ (κℕ 42))
    (id (‵ `ℕ))
    (？ (id (‵ `ℕ)))

source-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ² more-precise ⊑ less-precise
    ⦂ ℕᵗ ⊑ ℕᵗ ∶ I.ι⊑ι
source-imprecision =
  GTI.·⊑·ᴳ
    (GTI.ƛ⊑ƛᴳ {pA = I.ι⊑ι} {pB = I.ι⊑ι}
      (GTI.x⊑xᴳ GTI.Zⁱ))
    core-imprecision
    nat-consistent-star
    nat-consistent-star


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

less-function-compiled : Term 0
less-function-compiled =
  proj₁ (compile {Σ = store-empty} less-function-⊢)

less-function-compiled-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ less-function-compiled ⦂ (★ ⇒ ★)
less-function-compiled-⊢ =
  proj₂ (compile {Σ = store-empty} less-function-⊢)

more-precise-compiled-shape :
  more-precise-compiled ≡
    (C.ƛ (C.` 0)) C.·
      ((((C.Λ
          (C.ƛ
            ((C.ƛ (C.` 0)) C.·
              (C.` 0 C.⟨ symᶜ (star-consistent-X {Δ = 0}) ⟩))))
          C.⦂∀ X⇒★ [ ℕᵗ ]) C.·
          (C.$ (κℕ 42) C.⟨ id {μ = idᶜ} (‵ `ℕ) ⟩))
        C.⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩)
more-precise-compiled-shape = refl

less-precise-compiled-shape :
  less-precise-compiled ≡
    (C.ƛ (C.` 0)) C.·
      (((C.ƛ
        ((C.ƛ (C.` 0)) C.·
          (C.` 0 C.⟨ id {μ = idᶜ} ★ ⟩))) C.·
          (C.$ (κℕ 42) C.⟨ id {μ = idᶜ} (‵ `ℕ) ! ⟩))
        C.⟨ ？ (id {μ = idᶜ} (‵ `ℕ)) ⟩)
less-precise-compiled-shape = refl

more-precise-eval :
  Ex.evalBlame Ex.gas more-precise-compiled-⊢ ≡ just true
more-precise-eval = refl

less-precise-eval :
  Ex.evalNat Ex.gas less-precise-compiled-⊢ ≡ just 42
less-precise-eval = refl


------------------------------------------------------------------------
-- Operational checkpoints
------------------------------------------------------------------------

more-checkpoint₀ : Term 0
more-checkpoint₀ = more-precise-compiled

less-checkpoint₀ : Term 0
less-checkpoint₀ = less-precise-compiled

more-step₀ : Step.OneStep store-empty more-checkpoint₀
more-step₀ = Step.from-just-step (step? store-empty more-checkpoint₀) refl

more-checkpoint₁ : Term (Step.Δ′ more-step₀)
more-checkpoint₁ = Step.next more-step₀

less-checkpoint₁ : Term 0
less-checkpoint₁ = less-checkpoint₀

more-store₁ : TyStore (Step.Δ′ more-step₀)
more-store₁ = Step.store-after more-step₀

more-step₁ : Step.OneStep more-store₁ more-checkpoint₁
more-step₁ = Step.from-just-step (step? more-store₁ more-checkpoint₁) refl

more-checkpoint₂ : Term (Step.Δ′ more-step₁)
more-checkpoint₂ = Step.next more-step₁

less-checkpoint₂ : Term 0
less-checkpoint₂ = less-checkpoint₁

more-store₂ : TyStore (Step.Δ′ more-step₁)
more-store₂ = Step.store-after more-step₁

more-step₂ : Step.OneStep more-store₂ more-checkpoint₂
more-step₂ = Step.from-just-step (step? more-store₂ more-checkpoint₂) refl

more-checkpoint₃ : Term (Step.Δ′ more-step₂)
more-checkpoint₃ = Step.next more-step₂

less-checkpoint₃ : Term 0
less-checkpoint₃ = less-checkpoint₂

more-store₃ : TyStore (Step.Δ′ more-step₂)
more-store₃ = Step.store-after more-step₂

more-step₃ : Step.OneStep more-store₃ more-checkpoint₃
more-step₃ = Step.from-just-step (step? more-store₃ more-checkpoint₃) refl

less-step₀ : Step.OneStep store-empty less-checkpoint₃
less-step₀ = Step.from-just-step (step? store-empty less-checkpoint₃) refl

more-checkpoint₄ : Term (Step.Δ′ more-step₃)
more-checkpoint₄ = Step.next more-step₃

less-checkpoint₄ : Term (Step.Δ′ less-step₀)
less-checkpoint₄ = Step.next less-step₀

more-store₄ : TyStore (Step.Δ′ more-step₃)
more-store₄ = Step.store-after more-step₃

less-store₄ : TyStore (Step.Δ′ less-step₀)
less-store₄ = Step.store-after less-step₀

more-step₄ : Step.OneStep more-store₄ more-checkpoint₄
more-step₄ = Step.from-just-step (step? more-store₄ more-checkpoint₄) refl

less-step₁ : Step.OneStep less-store₄ less-checkpoint₄
less-step₁ = Step.from-just-step (step? less-store₄ less-checkpoint₄) refl

less-middle₅ : Term (Step.Δ′ less-step₁)
less-middle₅ = Step.next less-step₁

less-store-middle₅ : TyStore (Step.Δ′ less-step₁)
less-store-middle₅ = Step.store-after less-step₁

less-step₂ : Step.OneStep less-store-middle₅ less-middle₅
less-step₂ =
  Step.from-just-step (step? less-store-middle₅ less-middle₅) refl

more-checkpoint₅ : Term (Step.Δ′ more-step₄)
more-checkpoint₅ = Step.next more-step₄

less-checkpoint₅ : Term (Step.Δ′ less-step₂)
less-checkpoint₅ = Step.next less-step₂

more-store₅ : TyStore (Step.Δ′ more-step₄)
more-store₅ = Step.store-after more-step₄

less-store₅ : TyStore (Step.Δ′ less-step₂)
less-store₅ = Step.store-after less-step₂

more-step₅ : Step.OneStep more-store₅ more-checkpoint₅
more-step₅ = Step.from-just-step (step? more-store₅ more-checkpoint₅) refl

more-checkpoint₆ : Term (Step.Δ′ more-step₅)
more-checkpoint₆ = Step.next more-step₅

less-checkpoint₆ : Term (Step.Δ′ less-step₂)
less-checkpoint₆ = less-checkpoint₅

more-store₆ : TyStore (Step.Δ′ more-step₅)
more-store₆ = Step.store-after more-step₅

more-step₆ : Step.OneStep more-store₆ more-checkpoint₆
more-step₆ = Step.from-just-step (step? more-store₆ more-checkpoint₆) refl

less-step₃ : Step.OneStep less-store₅ less-checkpoint₆
less-step₃ = Step.from-just-step (step? less-store₅ less-checkpoint₆) refl

more-checkpoint₇ : Term (Step.Δ′ more-step₆)
more-checkpoint₇ = Step.next more-step₆

less-checkpoint₇ : Term (Step.Δ′ less-step₃)
less-checkpoint₇ = Step.next less-step₃

more-store₇ : TyStore (Step.Δ′ more-step₆)
more-store₇ = Step.store-after more-step₆

less-store₇ : TyStore (Step.Δ′ less-step₃)
less-store₇ = Step.store-after less-step₃

more-step₇ : Step.OneStep more-store₇ more-checkpoint₇
more-step₇ = Step.from-just-step (step? more-store₇ more-checkpoint₇) refl

less-step₄ : Step.OneStep less-store₇ less-checkpoint₇
less-step₄ = Step.from-just-step (step? less-store₇ less-checkpoint₇) refl

more-checkpoint₈ : Term (Step.Δ′ more-step₇)
more-checkpoint₈ = Step.next more-step₇

less-checkpoint₈ : Term (Step.Δ′ less-step₄)
less-checkpoint₈ = Step.next less-step₄

more-final : more-checkpoint₈ ≡ C.blame
more-final = refl

less-final : less-checkpoint₈ ≡ C.$ (κℕ 42)
less-final = refl


------------------------------------------------------------------------
-- Whole-term reduction segments
------------------------------------------------------------------------

more-checkpoint₀↠₁ :
  more-checkpoint₀ —↠[ bind (‵ `ℕ) ∷ [] ] more-checkpoint₁
more-checkpoint₀↠₁ =
  more-checkpoint₀
  —→[ bind (‵ `ℕ) ]⟨ Step.reduction more-step₀ ⟩
  more-checkpoint₁ ∎[]

less-checkpoint₀↠₁ : less-checkpoint₀ —↠[ [] ] less-checkpoint₁
less-checkpoint₀↠₁ = less-checkpoint₁ ∎[]

more-checkpoint₁↠₂ : more-checkpoint₁ —↠[ keep ∷ [] ] more-checkpoint₂
more-checkpoint₁↠₂ =
  more-checkpoint₁
  —→[ keep ]⟨ Step.reduction more-step₁ ⟩
  more-checkpoint₂ ∎[]

less-checkpoint₁↠₂ : less-checkpoint₁ —↠[ [] ] less-checkpoint₂
less-checkpoint₁↠₂ = less-checkpoint₂ ∎[]

more-checkpoint₂↠₃ : more-checkpoint₂ —↠[ keep ∷ [] ] more-checkpoint₃
more-checkpoint₂↠₃ =
  more-checkpoint₂
  —→[ keep ]⟨ Step.reduction more-step₂ ⟩
  more-checkpoint₃ ∎[]

less-checkpoint₂↠₃ : less-checkpoint₂ —↠[ [] ] less-checkpoint₃
less-checkpoint₂↠₃ = less-checkpoint₃ ∎[]

more-checkpoint₃↠₄ : more-checkpoint₃ —↠[ keep ∷ [] ] more-checkpoint₄
more-checkpoint₃↠₄ =
  more-checkpoint₃
  —→[ keep ]⟨ Step.reduction more-step₃ ⟩
  more-checkpoint₄ ∎[]

less-checkpoint₃↠₄ : less-checkpoint₃ —↠[ keep ∷ [] ] less-checkpoint₄
less-checkpoint₃↠₄ =
  less-checkpoint₃
  —→[ keep ]⟨ Step.reduction less-step₀ ⟩
  less-checkpoint₄ ∎[]

more-checkpoint₄↠₅ : more-checkpoint₄ —↠[ keep ∷ [] ] more-checkpoint₅
more-checkpoint₄↠₅ =
  more-checkpoint₄
  —→[ keep ]⟨ Step.reduction more-step₄ ⟩
  more-checkpoint₅ ∎[]

less-checkpoint₄↠₅ :
  less-checkpoint₄ —↠[ keep ∷ keep ∷ [] ] less-checkpoint₅
less-checkpoint₄↠₅ =
  less-checkpoint₄
  —→[ keep ]⟨ Step.reduction less-step₁ ⟩
  less-middle₅
  —→[ keep ]⟨ Step.reduction less-step₂ ⟩
  less-checkpoint₅ ∎[]

more-checkpoint₅↠₆ : more-checkpoint₅ —↠[ keep ∷ [] ] more-checkpoint₆
more-checkpoint₅↠₆ =
  more-checkpoint₅
  —→[ keep ]⟨ Step.reduction more-step₅ ⟩
  more-checkpoint₆ ∎[]

less-checkpoint₅↠₆ : less-checkpoint₅ —↠[ [] ] less-checkpoint₆
less-checkpoint₅↠₆ = less-checkpoint₆ ∎[]

more-checkpoint₆↠₇ : more-checkpoint₆ —↠[ keep ∷ [] ] more-checkpoint₇
more-checkpoint₆↠₇ =
  more-checkpoint₆
  —→[ keep ]⟨ Step.reduction more-step₆ ⟩
  more-checkpoint₇ ∎[]

less-checkpoint₆↠₇ : less-checkpoint₆ —↠[ keep ∷ [] ] less-checkpoint₇
less-checkpoint₆↠₇ =
  less-checkpoint₆
  —→[ keep ]⟨ Step.reduction less-step₃ ⟩
  less-checkpoint₇ ∎[]

more-checkpoint₇↠₈ : more-checkpoint₇ —↠[ keep ∷ [] ] more-checkpoint₈
more-checkpoint₇↠₈ =
  more-checkpoint₇
  —→[ keep ]⟨ Step.reduction more-step₇ ⟩
  more-checkpoint₈ ∎[]

less-checkpoint₇↠₈ : less-checkpoint₇ —↠[ keep ∷ [] ] less-checkpoint₈
less-checkpoint₇↠₈ =
  less-checkpoint₇
  —→[ keep ]⟨ Step.reduction less-step₄ ⟩
  less-checkpoint₈ ∎[]

more-reduction :
  more-checkpoint₀ —↠[
    bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ []
  ] more-checkpoint₈
more-reduction =
  more-checkpoint₀
  —→[ bind (‵ `ℕ) ]⟨ Step.reduction more-step₀ ⟩
  more-checkpoint₁
  —→[ keep ]⟨ Step.reduction more-step₁ ⟩
  more-checkpoint₂
  —→[ keep ]⟨ Step.reduction more-step₂ ⟩
  more-checkpoint₃
  —→[ keep ]⟨ Step.reduction more-step₃ ⟩
  more-checkpoint₄
  —→[ keep ]⟨ Step.reduction more-step₄ ⟩
  more-checkpoint₅
  —→[ keep ]⟨ Step.reduction more-step₅ ⟩
  more-checkpoint₆
  —→[ keep ]⟨ Step.reduction more-step₆ ⟩
  more-checkpoint₇
  —→[ keep ]⟨ Step.reduction more-step₇ ⟩
  more-checkpoint₈ ∎[]

less-reduction :
  less-checkpoint₀ —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
    less-checkpoint₈
less-reduction =
  less-checkpoint₀
  —→[ keep ]⟨ Step.reduction less-step₀ ⟩
  less-checkpoint₄
  —→[ keep ]⟨ Step.reduction less-step₁ ⟩
  less-middle₅
  —→[ keep ]⟨ Step.reduction less-step₂ ⟩
  less-checkpoint₅
  —→[ keep ]⟨ Step.reduction less-step₃ ⟩
  less-checkpoint₇
  —→[ keep ]⟨ Step.reduction less-step₄ ⟩
  less-checkpoint₈ ∎[]


------------------------------------------------------------------------
-- Runtime world and generated conversions
------------------------------------------------------------------------

base-context : Ctx
base-context = ⟨ 0 , store-empty , [] ⟩

source-only-world : (base-context ,ˢ ℕᵗ) ⊑ᶜ base-context
source-only-world = bindLeftᶜ emptyᶜ ℕᵗ

source-member : store-bind store-empty ℕᵗ ∋ Fin.zero ⦂ ℕᵗ
source-member = Z∋ refl

source-arrow-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    (Conv.seal Fin.zero ℕᵗ Conv.↦↑ Conv.id↑ ★)
source-arrow-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal source-member)
    (Conv.⊢↑-id-star source-member)

source-identity-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ] Conv.id↑ ★
source-identity-reveal⊢ = Conv.⊢↑-id-star source-member

source-conceal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↓[ Fin.zero ⦂ ℕᵗ ]
    Conv.seal Fin.zero ℕᵗ
source-conceal⊢ = Conv.⊢↓-seal source-member

source-arrow-reveal-active :
  revealGeneratorPosition source-arrow-reveal⊢ ≢ generator-absent
source-arrow-reveal-active ()

source-identity-reveal-absent :
  revealGeneratorPosition source-identity-reveal⊢ ≡ generator-absent
source-identity-reveal-absent = refl

source-conceal-active :
  concealGeneratorPosition source-conceal⊢ ≢ generator-absent
source-conceal-active ()

source-unoccupied : ∀ Xᴿ
  → toRenameᵗ (ηᴿᶜ source-only-world) Xᴿ
    ≢ toRenameᵗ (ηᴸᶜ source-only-world) Fin.zero
source-unoccupied ()


------------------------------------------------------------------------
-- Reusable subderivations
------------------------------------------------------------------------

result-function-imprecision :
  source-only-world CTI.⊢²
    C.ƛ (C.` 0) ⊑ C.ƛ (C.` 0) ∶
      I.⇒⊑⇒ (I.ι⊑ι {ι = `ℕ}) (I.ι⊑ι {ι = `ℕ})
result-function-imprecision =
  CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z)

lifted-body-imprecision :
  bind-termᶜ (liftLeftᶜ emptyᶜ) (I.X⊑★ refl) CTI.⊢²
    (C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ symᶜ (star-consistent-X {Δ = 0}) ⟩)
    ⊑ (C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ id {μ = idᶜ} ★ ⟩) ∶ I.★⊑★
lifted-body-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
      (CTI.x⊑x² {p = I.★⊑★} Z Z))
    (CTI.cast⊑cast²
      (symᶜ (star-consistent-X {Δ = 0}))
      (id {μ = idᶜ} ★)
      (CTI.x⊑x² {p = I.X⊑★ refl} Z Z)
      I.★⊑★)

lifted-function-imprecision :
  liftLeftᶜ emptyᶜ CTI.⊢²
    C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ symᶜ (star-consistent-X {Δ = 0}) ⟩))
    ⊑ C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ id {μ = idᶜ} ★ ⟩)) ∶ X⇒★⊑★⇒★
lifted-function-imprecision =
  CTI.ƛ⊑ƛ² lifted-body-imprecision

allocated-body-imprecision :
  bind-termᶜ source-only-world (I.X⊑★ refl) CTI.⊢²
    (C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ symᶜ (star-consistent-X {Δ = 0}) ⟩)
    ⊑ (C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ id {μ = idᶜ} ★ ⟩) ∶ I.★⊑★
allocated-body-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
      (CTI.x⊑x² {p = I.★⊑★} Z Z))
    (CTI.cast⊑cast²
      (symᶜ (star-consistent-X {Δ = 0}))
      (id {μ = idᶜ} ★)
      (CTI.x⊑x² {p = I.X⊑★ refl} Z Z)
      I.★⊑★)

allocated-function-imprecision :
  source-only-world CTI.⊢²
    C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ symᶜ (star-consistent-X {Δ = 0}) ⟩))
    ⊑ C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ id {μ = idᶜ} ★ ⟩)) ∶ X⇒★⊑★⇒★
allocated-function-imprecision =
  CTI.ƛ⊑ƛ² allocated-body-imprecision

source-arrow-function-imprecision :
  source-only-world CTI.⊢²
    (C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ symᶜ (star-consistent-X {Δ = 0}) ⟩))) C.↑
        (Conv.seal Fin.zero ℕᵗ Conv.↦↑ Conv.id↑ ★)
    ⊑ C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ id {μ = idᶜ} ★ ⟩)) ∶ ℕ⇒★⊑★⇒★
source-arrow-function-imprecision =
  CTI.reveal⊑-only²
    source-arrow-reveal⊢
    source-arrow-reveal-active
    refl
    source-unoccupied
    I.ι⊑★
    allocated-function-imprecision
    ℕ⇒★⊑★⇒★

initial-argument-imprecision :
  source-only-world CTI.⊢²
    C.$ (κℕ 42) C.⟨
      ↑ᶜ (symᶜ (id {μ = idᶜ} (‵ `ℕ))) ⟩
    ⊑ C.$ (κℕ 42) C.⟨ id {μ = idᶜ} (‵ `ℕ) ! ⟩ ∶ I.ι⊑★
initial-argument-imprecision =
  CTI.cast⊑cast²
    (↑ᶜ (symᶜ (id {μ = idᶜ} (‵ `ℕ))))
    (id {μ = idᶜ} (‵ `ℕ) !)
    (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
    I.ι⊑★

stripped-argument-imprecision :
  source-only-world CTI.⊢²
    C.$ (κℕ 42)
    ⊑ C.$ (κℕ 42) C.⟨ id {μ = idᶜ} (‵ `ℕ) ! ⟩ ∶ I.ι⊑★
stripped-argument-imprecision =
  CTI.⊑cast²
    (id {μ = idᶜ} (‵ `ℕ) !)
    (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
    I.ι⊑★

concealed-argument-imprecision :
  source-only-world CTI.⊢²
    C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ
    ⊑ C.$ (κℕ 42) C.⟨ id {μ = idᶜ} (‵ `ℕ) ! ⟩ ∶ I.X⊑★ refl
concealed-argument-imprecision =
  CTI.conceal⊑-only²
    source-conceal⊢
    source-conceal-active
    refl
    source-unoccupied
    I.ι⊑★
    stripped-argument-imprecision
    (I.X⊑★ refl)

casted-concealed-argument-imprecision :
  source-only-world CTI.⊢²
    (C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ)
      C.⟨ symᶜ (star-consistent-X {Δ = 0}) ⟩
    ⊑ (C.$ (κℕ 42) C.⟨ id {μ = idᶜ} (‵ `ℕ) ! ⟩)
      C.⟨ id {μ = idᶜ} ★ ⟩ ∶ I.★⊑★
casted-concealed-argument-imprecision =
  CTI.cast⊑cast²
    (symᶜ (star-consistent-X {Δ = 0}))
    (id {μ = idᶜ} ★)
    concealed-argument-imprecision
    I.★⊑★

source-tagged-argument-imprecision :
  source-only-world CTI.⊢²
    (C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ)
      C.⟨ symᶜ (star-consistent-X {Δ = 0}) ⟩
    ⊑ C.$ (κℕ 42) C.⟨ id {μ = idᶜ} (‵ `ℕ) ! ⟩ ∶ I.★⊑★
source-tagged-argument-imprecision =
  CTI.cast⊑²
    (symᶜ (star-consistent-X {Δ = 0}))
    concealed-argument-imprecision
    I.★⊑★


------------------------------------------------------------------------
-- Cast-term imprecision at every checkpoint
------------------------------------------------------------------------

checkpoint₀-imprecision :
  emptyᶜ CTI.⊢² more-checkpoint₀ ⊑ less-checkpoint₀ ∶ I.ι⊑ι
checkpoint₀-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (？ (id {μ = idᶜ} (‵ `ℕ)))
      (？ (id {μ = idᶜ} (‵ `ℕ)))
      (CTI.·⊑·²
        (CTI.•⊑²
          ∀X⇒★⊑★⇒★
          (CTI.Λ⊑²
            nonvar-fun
            X∈X⇒★
            (C.ƛ ((C.ƛ (C.` 0)) C.·
              (C.` 0 C.⟨ symᶜ (star-consistent-X {Δ = 0}) ⟩)))
            less-function-compiled-⊢
            lifted-function-imprecision
            ∀X⇒★⊑★⇒★)
          I.ι⊑★
          ℕ⇒★⊑★⇒★)
        (CTI.cast⊑cast²
          (id {μ = idᶜ} (‵ `ℕ))
          (id {μ = idᶜ} (‵ `ℕ) !)
          (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
          I.ι⊑★))
      I.ι⊑ι)

checkpoint₀-ladder : String
checkpoint₀-ladder = impLadderDefault checkpoint₀-imprecision

checkpoint₀-ladder-pinned :
  checkpoint₀-ladder ≡
    "⟨⟩\n" ++
    "source term       A           ηᴸA         ⊑ costs                  ηᴿB      B        target term\n" ++
    "────────────────  ──────────  ──────────  ───────────────────────  ───────  ───────  ───────────────\n" ++
    "□₁ · □₂           ℕ           ℕ           ℕ⊑ℕ                      ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □          (ℕ ⇒ ℕ)     (ℕ ⇒ ℕ)     ℕ⊑ℕ, ℕ⊑ℕ                 (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0              ℕ           ℕ           ℕ⊑ℕ                      ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩       ℕ           ℕ           ℕ⊑ℕ                      ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂         ★           ★           ★⊑★                      ★        ★          □₁ · □₂\n" ++
    "  ├ □ [ ℕ ]       (ℕ ⇒ ★)     (ℕ ⇒ ★)     ι⊑★, ★⊑★                 (★ ⇒ ★)  (★ ⇒ ★)    ├ ─\n" ++
    "  │ Λ□            ∀ (♭0 ⇒ ★)  ∀ (♭0 ⇒ ★)  ∀⊑(mark X⊑★ at ♭0, ★⊑★)  (★ ⇒ ★)  (★ ⇒ ★)    │ ─\n" ++
    "  │ λ♯0. □        (♭0 ⇒ ★)    (♭0 ⇒ ★)    mark X⊑★ at ♭0, ★⊑★      (★ ⇒ ★)  (★ ⇒ ★)    │ λ♯0. □\n" ++
    "  │ □₁ · □₂       ★           ★           ★⊑★                      ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □      (★ ⇒ ★)     (★ ⇒ ★)     ★⊑★, ★⊑★                 (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1          ★           ★           ★⊑★                      ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ ♭0↦★ ⟩  ★           ★           ★⊑★                      ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0          ♭0          ♭0          mark X⊑★ at ♭0           ★        ★          │   ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩     ℕ           ℕ           ι⊑★                      ★        ★          └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42            ℕ           ℕ           ℕ⊑ℕ                      ℕ        ℕ            42"
checkpoint₀-ladder-pinned = refl
checkpoint₁-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₁ ⊑ less-checkpoint₁ ∶ I.ι⊑ι
checkpoint₁-imprecision =
  CTI.·⊑·²
    result-function-imprecision
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ)
        (symᶜ (nat-consistent-star {Δ = 0})))
      (symᶜ (nat-consistent-star {Δ = 0}))
      (CTI.·⊑·²
        source-arrow-function-imprecision
        initial-argument-imprecision)
      I.ι⊑ι)

checkpoint₁-ladder : String
checkpoint₁-ladder = impLadderDefault checkpoint₁-imprecision

checkpoint₁-ladder-pinned :
  checkpoint₁-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term      A        ηᴸA      ⊑ costs                       ηᴿB      B        target term\n" ++
    "───────────────  ───────  ───────  ────────────────────────────  ───────  ───────  ───────────────\n" ++
    "□₁ · □₂          ℕ        ℕ        ℕ⊑ℕ                           ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                      (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0             ℕ        ℕ        ℕ⊑ℕ                           ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩      ℕ        ℕ        ℕ⊑ℕ                           ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂        ★        ★        ★⊑★                           ★        ★          □₁ · □₂\n" ++
    "  ├ □ ↑ ⇒-rev    (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + target unoccupied  (★ ⇒ ★)  (★ ⇒ ★)    ├ ─\n" ++
    "  │ λ♯0. □       (X ⇒ ★)  (X ⇒ ★)  mark X⊑★ at X, ★⊑★            (★ ⇒ ★)  (★ ⇒ ★)    │ λ♯0. □\n" ++
    "  │ □₁ · □₂      ★        ★        ★⊑★                           ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □     (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                      (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1         ★        ★        ★⊑★                           ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ X↦★ ⟩  ★        ★        ★⊑★                           ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0         X        X        mark X⊑★ at X                 ★        ★          │   ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩    ℕ        ℕ        ι⊑★                           ★        ★          └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42           ℕ        ℕ        ℕ⊑ℕ                           ℕ        ℕ            42"
checkpoint₁-ladder-pinned = refl
checkpoint₂-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₂ ⊑ less-checkpoint₂ ∶ I.ι⊑ι
checkpoint₂-imprecision =
  CTI.·⊑·²
    result-function-imprecision
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ)
        (symᶜ (nat-consistent-star {Δ = 0})))
      (symᶜ (nat-consistent-star {Δ = 0}))
      (CTI.·⊑·²
        source-arrow-function-imprecision
        stripped-argument-imprecision)
      I.ι⊑ι)

checkpoint₂-ladder : String
checkpoint₂-ladder = impLadderDefault checkpoint₂-imprecision

checkpoint₂-ladder-pinned :
  checkpoint₂-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term      A        ηᴸA      ⊑ costs                       ηᴿB      B        target term\n" ++
    "───────────────  ───────  ───────  ────────────────────────────  ───────  ───────  ───────────────\n" ++
    "□₁ · □₂          ℕ        ℕ        ℕ⊑ℕ                           ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                      (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0             ℕ        ℕ        ℕ⊑ℕ                           ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩      ℕ        ℕ        ℕ⊑ℕ                           ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂        ★        ★        ★⊑★                           ★        ★          □₁ · □₂\n" ++
    "  ├ □ ↑ ⇒-rev    (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + target unoccupied  (★ ⇒ ★)  (★ ⇒ ★)    ├ ─\n" ++
    "  │ λ♯0. □       (X ⇒ ★)  (X ⇒ ★)  mark X⊑★ at X, ★⊑★            (★ ⇒ ★)  (★ ⇒ ★)    │ λ♯0. □\n" ++
    "  │ □₁ · □₂      ★        ★        ★⊑★                           ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □     (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                      (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1         ★        ★        ★⊑★                           ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ X↦★ ⟩  ★        ★        ★⊑★                           ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0         X        X        mark X⊑★ at X                 ★        ★          │   ♯0\n" ++
    "  └ ─            ℕ        ℕ        ι⊑★                           ★        ★          └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42           ℕ        ℕ        ℕ⊑ℕ                           ℕ        ℕ            42"
checkpoint₂-ladder-pinned = refl
identity-reveal-application-imprecision :
  source-only-world CTI.⊢²
    ((C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ symᶜ (star-consistent-X {Δ = 0}) ⟩))) C.·
      (C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ))
      C.↑ Conv.id↑ ★
    ⊑ (C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ id {μ = idᶜ} ★ ⟩))) C.·
      (C.$ (κℕ 42) C.⟨ id {μ = idᶜ} (‵ `ℕ) ! ⟩) ∶ I.★⊑★
identity-reveal-application-imprecision =
  CTI.reveal⊑-identity
    source-identity-reveal⊢
    source-identity-reveal-absent
    (CTI.·⊑·²
      allocated-function-imprecision
      concealed-argument-imprecision)
    I.★⊑★

checkpoint₃-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₃ ⊑ less-checkpoint₃ ∶ I.ι⊑ι
checkpoint₃-imprecision =
  CTI.·⊑·²
    result-function-imprecision
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ)
        (symᶜ (nat-consistent-star {Δ = 0})))
      (symᶜ (nat-consistent-star {Δ = 0}))
      identity-reveal-application-imprecision
      I.ι⊑ι)

checkpoint₃-ladder : String
checkpoint₃-ladder = impLadderDefault checkpoint₃-imprecision

checkpoint₃-ladder-pinned :
  checkpoint₃-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term      A        ηᴸA      ⊑ costs                            ηᴿB      B        target term\n" ++
    "───────────────  ───────  ───────  ─────────────────────────────────  ───────  ───────  ───────────────\n" ++
    "□₁ · □₂          ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                           (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0             ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩      ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ↑ id         ★        ★        ★⊑★ + generator absent             ★        ★          ─\n" ++
    "  □₁ · □₂        ★        ★        ★⊑★                                ★        ★          □₁ · □₂\n" ++
    "  ├ λ♯0. □       (X ⇒ ★)  (X ⇒ ★)  mark X⊑★ at X, ★⊑★                 (★ ⇒ ★)  (★ ⇒ ★)    ├ λ♯0. □\n" ++
    "  │ □₁ · □₂      ★        ★        ★⊑★                                ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □     (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1         ★        ★        ★⊑★                                ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ X↦★ ⟩  ★        ★        ★⊑★                                ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0         X        X        mark X⊑★ at X                      ★        ★          │   ♯0\n" ++
    "  └ □ ↓ seal X   X        X        mark X⊑★ at X + target unoccupied  ★        ★          └ ─\n" ++
    "    ─            ℕ        ℕ        ι⊑★                                ★        ★            □ ⟨ ℕ↦★ ⟩\n" ++
    "    42           ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ            42"
checkpoint₃-ladder-pinned = refl
checkpoint₄-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₄ ⊑ less-checkpoint₄ ∶ I.ι⊑ι
checkpoint₄-imprecision =
  CTI.·⊑·²
    result-function-imprecision
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ)
        (symᶜ (nat-consistent-star {Δ = 0})))
      (symᶜ (nat-consistent-star {Δ = 0}))
      (CTI.reveal⊑-identity
        source-identity-reveal⊢
        source-identity-reveal-absent
        (CTI.·⊑·²
          (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
            (CTI.x⊑x² {p = I.★⊑★} Z Z))
          casted-concealed-argument-imprecision)
        I.★⊑★)
      I.ι⊑ι)

checkpoint₄-ladder : String
checkpoint₄-ladder = impLadderDefault checkpoint₄-imprecision

checkpoint₄-ladder-pinned :
  checkpoint₄-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term     A        ηᴸA      ⊑ costs                            ηᴿB      B        target term\n" ++
    "──────────────  ───────  ───────  ─────────────────────────────────  ───────  ───────  ─────────────\n" ++
    "□₁ · □₂         ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □        (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                           (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0            ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩     ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ↑ id        ★        ★        ★⊑★ + generator absent             ★        ★          ─\n" ++
    "  □₁ · □₂       ★        ★        ★⊑★                                ★        ★          □₁ · □₂\n" ++
    "  ├ λ♯0. □      (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)    ├ λ♯0. □\n" ++
    "  │ ♯0          ★        ★        ★⊑★                                ★        ★          │ ♯0\n" ++
    "  └ □ ⟨ X↦★ ⟩   ★        ★        ★⊑★                                ★        ★          └ □ ⟨ ★↦★ ⟩\n" ++
    "    □ ↓ seal X  X        X        mark X⊑★ at X + target unoccupied  ★        ★            ─\n" ++
    "    ─           ℕ        ℕ        ι⊑★                                ★        ★            □ ⟨ ℕ↦★ ⟩\n" ++
    "    42          ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ            42"
checkpoint₄-ladder-pinned = refl
checkpoint₅-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₅ ⊑ less-checkpoint₅ ∶ I.ι⊑ι
checkpoint₅-imprecision =
  CTI.·⊑·²
    result-function-imprecision
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ)
        (symᶜ (nat-consistent-star {Δ = 0})))
      (symᶜ (nat-consistent-star {Δ = 0}))
      (CTI.reveal⊑-identity
        source-identity-reveal⊢
        source-identity-reveal-absent
        source-tagged-argument-imprecision
        I.★⊑★)
      I.ι⊑ι)

checkpoint₅-ladder : String
checkpoint₅-ladder = impLadderDefault checkpoint₅-imprecision

checkpoint₅-ladder-pinned :
  checkpoint₅-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term   A        ηᴸA      ⊑ costs                            ηᴿB      B        target term\n" ++
    "────────────  ───────  ───────  ─────────────────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂       ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □      (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                           (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0          ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩   ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ↑ id      ★        ★        ★⊑★ + generator absent             ★        ★          ─\n" ++
    "  □ ⟨ X↦★ ⟩   ★        ★        ★⊑★                                ★        ★          ─\n" ++
    "  □ ↓ seal X  X        X        mark X⊑★ at X + target unoccupied  ★        ★          ─\n" ++
    "  ─           ℕ        ℕ        ι⊑★                                ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42          ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ          42"
checkpoint₅-ladder-pinned = refl
checkpoint₆-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₆ ⊑ less-checkpoint₆ ∶ I.ι⊑ι
checkpoint₆-imprecision =
  CTI.·⊑·²
    result-function-imprecision
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ)
        (symᶜ (nat-consistent-star {Δ = 0})))
      (symᶜ (nat-consistent-star {Δ = 0}))
      source-tagged-argument-imprecision
      I.ι⊑ι)

checkpoint₆-ladder : String
checkpoint₆-ladder = impLadderDefault checkpoint₆-imprecision

checkpoint₆-ladder-pinned :
  checkpoint₆-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term   A        ηᴸA      ⊑ costs                            ηᴿB      B        target term\n" ++
    "────────────  ───────  ───────  ─────────────────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂       ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □      (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                           (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0          ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩   ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ X↦★ ⟩   ★        ★        ★⊑★                                ★        ★          ─\n" ++
    "  □ ↓ seal X  X        X        mark X⊑★ at X + target unoccupied  ★        ★          ─\n" ++
    "  ─           ℕ        ℕ        ι⊑★                                ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42          ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ          42"
checkpoint₆-ladder-pinned = refl
checkpoint₇-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₇ ⊑ less-checkpoint₇ ∶ I.ι⊑ι
checkpoint₇-imprecision =
  CTI.·⊑·²
    result-function-imprecision
    (CTI.blame⊑² (C.⊢$ (κℕ 42)) I.ι⊑ι)

checkpoint₇-ladder : String
checkpoint₇-ladder = impLadderDefault checkpoint₇-imprecision

checkpoint₇-ladder-pinned :
  checkpoint₇-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs   ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        │ ♯0\n" ++
    "└ blame      ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        └ 42"
checkpoint₇-ladder-pinned = refl
checkpoint₈-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₈ ⊑ less-checkpoint₈ ∶ I.ι⊑ι
checkpoint₈-imprecision =
  CTI.blame⊑² (C.⊢$ (κℕ 42)) I.ι⊑ι

checkpoint₈-ladder : String
checkpoint₈-ladder = impLadderDefault checkpoint₈-imprecision

checkpoint₈-ladder-pinned :
  checkpoint₈-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term\n" ++
    "───────────  ─  ───  ───────  ───  ─  ───────────\n" ++
    "blame        ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  42"
checkpoint₈-ladder-pinned = refl
