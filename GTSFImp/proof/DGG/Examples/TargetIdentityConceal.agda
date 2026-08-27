{-# OPTIONS --safe #-}

module proof.DGG.Examples.TargetIdentityConceal where

-- File Charter:
--   * Checks the target-only counterpart of SourceIdentityConceal.
--   * Uses the annotated-identity idiom to cast a polymorphic higher-order
--     value to a dynamic higher-order function on the less-precise side.
--   * Records one checkpoint after every more-precise reduction; target
--     catch-up exposes a target-only structural-identity conceal.

import Data.Fin as Fin
open import Data.Bool using (false)
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
  (keep; bind; applyEnv; applyConsistency; applyTerm; []; _∷_;
   _—↠[_]_; _—→[_]⟨_⟩_;
   _∎[])
open import Eval using (step?)
import Example as Ex
import proof.DGG.OneStep as Step
import proof.DGG.CastTermImprecision as CTI
import proof.DGG.Examples.TargetIdentityReveal as TIR
open import proof.DGG.World
open import proof.DGG.SourceRebase using (source-rebase-now)
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition;
   concealGeneratorPosition)
open import proof.DGG.ImpLadder using (impLadderDefault)

open GTI using () renaming
  (_∣_⊢ᴳ_⊑_⦂_⊑_∶_ to _∣_⊢ᴳ²_⊑_⦂_⊑_∶_)


------------------------------------------------------------------------
-- Types and source programs
------------------------------------------------------------------------

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

Xᵗ : ∀ {Δ} → Ty (Nat.suc Δ)
Xᵗ = ＇ Fin.zero

X⇒★ : ∀ {Δ} → Ty (Nat.suc Δ)
X⇒★ = Xᵗ ⇒ ★

higher-X : ∀ {Δ} → Ty (Nat.suc Δ)
higher-X = X⇒★ ⇒ X⇒★

∀higher-X : ∀ {Δ} → Ty Δ
∀higher-X = `∀ higher-X

dynamic-function : ∀ {Δ} → Ty Δ
dynamic-function = ★ ⇒ ★

higher-dynamic : ∀ {Δ} → Ty Δ
higher-dynamic = dynamic-function ⇒ dynamic-function

X∈higher-X : ∀ {Δ} → Fin.zero ∈ᵗ higher-X {Δ}
X∈higher-X = ∈-fun-left (∈-fun-left var-∈)

ℓ-inner : Label
ℓ-inner = 0

ℓ-cast : Label
ℓ-cast = 1

ℓ-higher : Label
ℓ-higher = 2

ℓ-data : Label
ℓ-data = 3

ℓ-result : Label
ℓ-result = 4

more-precise : GTerm 0
more-precise =
  (ƛ ℕᵗ ⇒ ` 0) ·[ ℓ-result ]
    ((((((ƛ ∀higher-X ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0))) `[ ℕᵗ ]) ·[ ℓ-higher ]
      (ƛ ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      ·[ ℓ-data ] $ (κℕ 42)))

less-precise : GTerm 0
less-precise =
  (ƛ ℕᵗ ⇒ ` 0) ·[ ℓ-result ]
    (((((ƛ higher-dynamic ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0))) ·[ ℓ-higher ]
      (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      ·[ ℓ-data ] $ (κℕ 42)))


------------------------------------------------------------------------
-- Source typing and imprecision
------------------------------------------------------------------------

star-consistent-X : ∀ {Δ} → ★ ∼ Xᵗ {Δ}
star-consistent-X = total-from-★ (from★-★∼X∼★ refl)

nat-consistent-star : ∀ {Δ} → ℕᵗ {Δ} ∼ ★
nat-consistent-star = total-to-★ to★-ι

star-consistent-nat : ∀ {Δ} → ★ ∼ ℕᵗ {Δ}
star-consistent-nat = total-from-★ from★-ι

flip-inst-★?X : ∀ {Δ} {μ : Env∼ Δ}
  → flipᵐ (instᵐ μ) ⊢ ★ ∼ Xᵗ
flip-inst-★?X =
  ？_ ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ ★∼G = ★∼Xᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Bns = nonstar-X ⦄

inst-X! : ∀ {Δ} {μ : Env∼ Δ}
  → instᵐ μ ⊢ Xᵗ ∼ ★
inst-X! =
  _! ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = X∼★ᵍ refl ⦄
    (id (＇ Fin.zero)) ⦃ Ans = nonstar-X ⦄

∀higher-X∼higher-dynamic : ∀ {Δ}
  → ∀higher-X {Δ} ∼ higher-dynamic
∀higher-X∼higher-dynamic =
  inst_
    ⦃ Anv = nonvar-fun ⦄
    ⦃ z∈A = X∈higher-X ⦄
    ((sym∼ flip-inst-★?X ↦ id ★) ↦
      (flip-inst-★?X ↦ id ★))
    (λ ())

higher-dynamic∼∀higher-X : ∀ {Δ}
  → higher-dynamic {Δ} ∼ ∀higher-X
higher-dynamic∼∀higher-X = symᶜ ∀higher-X∼higher-dynamic

∀higher-X∼∀higher-X : ∀ {Δ}
  → ∀higher-X {Δ} ∼ ∀higher-X
∀higher-X∼∀higher-X =
  ∀ᶜ ((id (＇ Fin.zero) ↦ id ★) ↦
    (id (＇ Fin.zero) ↦ id ★))

poly-⊢ : 0 ∣ [] ⊢ᴳ Λ (ƛ X⇒★ ⇒ ` 0) ⦂ ∀higher-X
poly-⊢ =
  ⊢Λ {zero∈A = X∈higher-X}
    (ƛ X⇒★ ⇒ ` 0) (⊢ƛ (⊢` Z))

more-argument-⊢ :
  0 ∣ [] ⊢ᴳ
    (ƛ ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
    ⦂ (ℕᵗ ⇒ ★)
more-argument-⊢ =
  ⊢ƛ (⊢· (⊢ƛ (⊢` Z)) (⊢` Z) star-consistent-nat)

less-argument-⊢ :
  0 ∣ [] ⊢ᴳ
    (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
    ⦂ dynamic-function
less-argument-⊢ =
  ⊢ƛ (⊢· (⊢ƛ (⊢` Z)) (⊢` Z) (id ★))

more-cast-⊢ :
  0 ∣ [] ⊢ᴳ
    ((ƛ ∀higher-X ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0))) ⦂ ∀higher-X
more-cast-⊢ =
  ⊢· (⊢ƛ (⊢` Z)) poly-⊢ ∀higher-X∼∀higher-X

less-cast-⊢ :
  0 ∣ [] ⊢ᴳ
    ((ƛ higher-dynamic ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0))) ⦂ higher-dynamic
less-cast-⊢ =
  ⊢· (⊢ƛ (⊢` Z)) poly-⊢ higher-dynamic∼∀higher-X

more-higher-core-⊢ :
  0 ∣ [] ⊢ᴳ
    ((((ƛ ∀higher-X ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0))) `[ ℕᵗ ]) ·[ ℓ-higher ]
      (ƛ ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
    ⦂ (ℕᵗ ⇒ ★)
more-higher-core-⊢ =
  ⊢· (⊢• more-cast-⊢) more-argument-⊢
    (id (‵ `ℕ) ↦ id ★)

less-higher-core-⊢ :
  0 ∣ [] ⊢ᴳ
    (((ƛ higher-dynamic ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0))) ·[ ℓ-higher ]
      (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
    ⦂ dynamic-function
less-higher-core-⊢ =
  ⊢· less-cast-⊢ less-argument-⊢
    (id ★ ↦ id ★)

more-core-⊢ :
  0 ∣ [] ⊢ᴳ
    (((((ƛ ∀higher-X ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0))) `[ ℕᵗ ]) ·[ ℓ-higher ]
      (ƛ ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      ·[ ℓ-data ] $ (κℕ 42)) ⦂ ★
more-core-⊢ =
  ⊢· more-higher-core-⊢ (⊢$ (κℕ 42))
    (id (‵ `ℕ))

less-core-⊢ :
  0 ∣ [] ⊢ᴳ
    ((((ƛ higher-dynamic ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0))) ·[ ℓ-higher ]
      (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      ·[ ℓ-data ] $ (κℕ 42)) ⦂ ★
less-core-⊢ =
  ⊢· less-higher-core-⊢ (⊢$ (κℕ 42))
    (？ (id (‵ `ℕ)))

more-precise-⊢ : 0 ∣ [] ⊢ᴳ more-precise ⦂ ℕᵗ
more-precise-⊢ =
  ⊢· (⊢ƛ (⊢` Z)) more-core-⊢ nat-consistent-star

less-precise-⊢ : 0 ∣ [] ⊢ᴳ less-precise ⦂ ℕᵗ
less-precise-⊢ =
  ⊢· (⊢ƛ (⊢` Z)) less-core-⊢ nat-consistent-star

X⇒★⊑X⇒★ : ∀ {Δ} {μ : I.ImpEnv (Nat.suc Δ)}
  → μ I.⊢ X⇒★ ⊑ X⇒★
X⇒★⊑X⇒★ = I.⇒⊑⇒ I.X⊑X I.★⊑★

higher-X⊑higher-X : ∀ {Δ} {μ : I.ImpEnv (Nat.suc Δ)}
  → μ I.⊢ higher-X ⊑ higher-X
higher-X⊑higher-X = I.⇒⊑⇒ X⇒★⊑X⇒★ X⇒★⊑X⇒★

∀higher-X⊑∀higher-X : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ∀higher-X ⊑ ∀higher-X
∀higher-X⊑∀higher-X = I.∀⊑∀ higher-X⊑higher-X

X⇒★⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → I.instᵐ μ I.⊢ X⇒★ ⊑ dynamic-function
X⇒★⊑★⇒★ = I.⇒⊑⇒ (I.X⊑★ refl) I.★⊑★

higher-X⊑higher-dynamic : ∀ {Δ} {μ : I.ImpEnv Δ}
  → I.instᵐ μ I.⊢ higher-X ⊑ higher-dynamic
higher-X⊑higher-dynamic =
  I.⇒⊑⇒ X⇒★⊑★⇒★ X⇒★⊑★⇒★

∀higher-X⊑higher-dynamic : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ∀higher-X ⊑ higher-dynamic
∀higher-X⊑higher-dynamic =
  I.∀⊑ nonvar-fun X∈higher-X higher-X⊑higher-dynamic

ℕ⇒★⊑★⇒★ : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ (ℕᵗ ⇒ ★) ⊑ dynamic-function
ℕ⇒★⊑★⇒★ = I.⇒⊑⇒ I.ι⊑★ I.★⊑★

higher-ℕ⊑higher-dynamic : ∀ {Δ} {μ : I.ImpEnv Δ}
  → μ I.⊢ ((ℕᵗ ⇒ ★) ⇒ (ℕᵗ ⇒ ★)) ⊑ higher-dynamic
higher-ℕ⊑higher-dynamic =
  I.⇒⊑⇒ ℕ⇒★⊑★⇒★ ℕ⇒★⊑★⇒★

poly-imprecision :
  I.idᵐ {Δ = 0} ∣ [] ⊢ᴳ²
    Λ (ƛ X⇒★ ⇒ ` 0) ⊑ Λ (ƛ X⇒★ ⇒ ` 0)
    ⦂ ∀higher-X ⊑ ∀higher-X ∶ ∀higher-X⊑∀higher-X
poly-imprecision =
  GTI.Λ⊑Λᴳ {p = higher-X⊑higher-X} GTI.lift-[]
    (ƛ X⇒★ ⇒ ` 0) (ƛ X⇒★ ⇒ ` 0)
    X∈higher-X X∈higher-X
    (GTI.ƛ⊑ƛᴳ (GTI.x⊑xᴳ GTI.Zⁱ))

cast-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ²
    ((ƛ ∀higher-X ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0)))
    ⊑ ((ƛ higher-dynamic ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0)))
    ⦂ ∀higher-X ⊑ higher-dynamic ∶ ∀higher-X⊑higher-dynamic
cast-imprecision =
  GTI.·⊑·ᴳ
    (GTI.ƛ⊑ƛᴳ
      {pA = ∀higher-X⊑higher-dynamic}
      {pB = ∀higher-X⊑higher-dynamic}
      (GTI.x⊑xᴳ GTI.Zⁱ))
    poly-imprecision
    ∀higher-X∼∀higher-X
    higher-dynamic∼∀higher-X

argument-imprecision :
  I.idᵐ {Δ = 0} ∣ [] ⊢ᴳ²
    (ƛ ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
    ⊑ (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0))
    ⦂ (ℕᵗ ⇒ ★) ⊑ dynamic-function ∶ ℕ⇒★⊑★⇒★
argument-imprecision =
  GTI.ƛ⊑ƛᴳ {pA = I.ι⊑★} {pB = I.★⊑★}
    (GTI.·⊑·ᴳ
      (GTI.ƛ⊑ƛᴳ {pA = I.★⊑★} {pB = I.★⊑★}
        (GTI.x⊑xᴳ GTI.Zⁱ))
      (GTI.x⊑xᴳ GTI.Zⁱ)
      star-consistent-nat
      (id ★))

higher-core-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ²
    ((((ƛ ∀higher-X ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0))) `[ ℕᵗ ]) ·[ ℓ-higher ]
      (ƛ ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
    ⊑ (((ƛ higher-dynamic ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0))) ·[ ℓ-higher ]
      (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
    ⦂ (ℕᵗ ⇒ ★) ⊑ dynamic-function ∶ ℕ⇒★⊑★⇒★
higher-core-imprecision =
  GTI.·⊑·ᴳ
    (GTI.[]⊑ᴳ cast-imprecision I.ι⊑★
      higher-ℕ⊑higher-dynamic)
    argument-imprecision
    (id (‵ `ℕ) ↦ id ★)
    (id ★ ↦ id ★)

core-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ²
    (((((ƛ ∀higher-X ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0))) `[ ℕᵗ ]) ·[ ℓ-higher ]
      (ƛ ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      ·[ ℓ-data ] $ (κℕ 42))
    ⊑ ((((ƛ higher-dynamic ⇒ ` 0) ·[ ℓ-cast ]
      (Λ (ƛ X⇒★ ⇒ ` 0))) ·[ ℓ-higher ]
      (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      ·[ ℓ-data ] $ (κℕ 42))
    ⦂ ★ ⊑ ★ ∶ I.★⊑★
core-imprecision =
  GTI.·⊑·ᴳ higher-core-imprecision
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

more-argument-compiled-shape :
  proj₁ (compile {Σ = store-empty} more-argument-⊢) ≡
    C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ id (‵ `ℕ) ! ⟩))
more-argument-compiled-shape = refl

less-argument-compiled-shape :
  proj₁ (compile {Σ = store-empty} less-argument-⊢) ≡
    C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ id ★ ⟩))
less-argument-compiled-shape = refl

more-precise-eval :
  Ex.evalBlame Ex.gas more-precise-compiled-⊢ ≡ Data.Maybe.just false
more-precise-eval = refl

less-precise-eval :
  Ex.evalBlame Ex.gas less-precise-compiled-⊢ ≡ Data.Maybe.just false
less-precise-eval = refl


------------------------------------------------------------------------
-- Executable traces
------------------------------------------------------------------------

more-checkpoint₀ : Term 0
more-checkpoint₀ = more-precise-compiled

more-store₀ = store-empty

more-step₀ : Step.OneStep more-store₀ more-checkpoint₀
more-step₀ =
  Step.from-just-step (step? more-store₀ more-checkpoint₀) refl

more-checkpoint₁ : Term (Step.Δ′ more-step₀)
more-checkpoint₁ = Step.next more-step₀

more-store₁ = Step.store-after more-step₀

more-step₁ : Step.OneStep more-store₁ more-checkpoint₁
more-step₁ =
  Step.from-just-step (step? more-store₁ more-checkpoint₁) refl

more-checkpoint₂ : Term (Step.Δ′ more-step₁)
more-checkpoint₂ = Step.next more-step₁

more-store₂ = Step.store-after more-step₁

more-step₂ : Step.OneStep more-store₂ more-checkpoint₂
more-step₂ =
  Step.from-just-step (step? more-store₂ more-checkpoint₂) refl

more-checkpoint₃ : Term (Step.Δ′ more-step₂)
more-checkpoint₃ = Step.next more-step₂

more-store₃ = Step.store-after more-step₂

more-step₃ : Step.OneStep more-store₃ more-checkpoint₃
more-step₃ =
  Step.from-just-step (step? more-store₃ more-checkpoint₃) refl

more-checkpoint₄ : Term (Step.Δ′ more-step₃)
more-checkpoint₄ = Step.next more-step₃

more-store₄ = Step.store-after more-step₃

more-step₄ : Step.OneStep more-store₄ more-checkpoint₄
more-step₄ =
  Step.from-just-step (step? more-store₄ more-checkpoint₄) refl

more-checkpoint₅ : Term (Step.Δ′ more-step₄)
more-checkpoint₅ = Step.next more-step₄

more-store₅ = Step.store-after more-step₄

more-step₅ : Step.OneStep more-store₅ more-checkpoint₅
more-step₅ =
  Step.from-just-step (step? more-store₅ more-checkpoint₅) refl

more-checkpoint₆ : Term (Step.Δ′ more-step₅)
more-checkpoint₆ = Step.next more-step₅

more-store₆ = Step.store-after more-step₅

more-step₆ : Step.OneStep more-store₆ more-checkpoint₆
more-step₆ =
  Step.from-just-step (step? more-store₆ more-checkpoint₆) refl

more-checkpoint₇ : Term (Step.Δ′ more-step₆)
more-checkpoint₇ = Step.next more-step₆

more-store₇ = Step.store-after more-step₆

more-step₇ : Step.OneStep more-store₇ more-checkpoint₇
more-step₇ =
  Step.from-just-step (step? more-store₇ more-checkpoint₇) refl

more-checkpoint₈ : Term (Step.Δ′ more-step₇)
more-checkpoint₈ = Step.next more-step₇

more-store₈ = Step.store-after more-step₇

more-step₈ : Step.OneStep more-store₈ more-checkpoint₈
more-step₈ =
  Step.from-just-step (step? more-store₈ more-checkpoint₈) refl

more-checkpoint₉ : Term (Step.Δ′ more-step₈)
more-checkpoint₉ = Step.next more-step₈

more-store₉ = Step.store-after more-step₈

more-step₉ : Step.OneStep more-store₉ more-checkpoint₉
more-step₉ =
  Step.from-just-step (step? more-store₉ more-checkpoint₉) refl

more-checkpoint₁₀ : Term (Step.Δ′ more-step₉)
more-checkpoint₁₀ = Step.next more-step₉

more-store₁₀ = Step.store-after more-step₉

more-step₁₀ : Step.OneStep more-store₁₀ more-checkpoint₁₀
more-step₁₀ =
  Step.from-just-step (step? more-store₁₀ more-checkpoint₁₀) refl

more-checkpoint₁₁ : Term (Step.Δ′ more-step₁₀)
more-checkpoint₁₁ = Step.next more-step₁₀

more-store₁₁ = Step.store-after more-step₁₀

more-step₁₁ : Step.OneStep more-store₁₁ more-checkpoint₁₁
more-step₁₁ =
  Step.from-just-step (step? more-store₁₁ more-checkpoint₁₁) refl

more-checkpoint₁₂ : Term (Step.Δ′ more-step₁₁)
more-checkpoint₁₂ = Step.next more-step₁₁

more-store₁₂ = Step.store-after more-step₁₁

more-step₁₂ : Step.OneStep more-store₁₂ more-checkpoint₁₂
more-step₁₂ =
  Step.from-just-step (step? more-store₁₂ more-checkpoint₁₂) refl

more-checkpoint₁₃ : Term (Step.Δ′ more-step₁₂)
more-checkpoint₁₃ = Step.next more-step₁₂

more-store₁₃ = Step.store-after more-step₁₂

more-step₁₃ : Step.OneStep more-store₁₃ more-checkpoint₁₃
more-step₁₃ =
  Step.from-just-step (step? more-store₁₃ more-checkpoint₁₃) refl

more-checkpoint₁₄ : Term (Step.Δ′ more-step₁₃)
more-checkpoint₁₄ = Step.next more-step₁₃

more-store₁₄ = Step.store-after more-step₁₃

more-step₁₄ : Step.OneStep more-store₁₄ more-checkpoint₁₄
more-step₁₄ =
  Step.from-just-step (step? more-store₁₄ more-checkpoint₁₄) refl

more-checkpoint₁₅ : Term (Step.Δ′ more-step₁₄)
more-checkpoint₁₅ = Step.next more-step₁₄

more-store₁₅ = Step.store-after more-step₁₄

more-step₁₅ : Step.OneStep more-store₁₅ more-checkpoint₁₅
more-step₁₅ =
  Step.from-just-step (step? more-store₁₅ more-checkpoint₁₅) refl

more-checkpoint₁₆ : Term (Step.Δ′ more-step₁₅)
more-checkpoint₁₆ = Step.next more-step₁₅

more-store₁₆ = Step.store-after more-step₁₅

more-step₁₆ : Step.OneStep more-store₁₆ more-checkpoint₁₆
more-step₁₆ =
  Step.from-just-step (step? more-store₁₆ more-checkpoint₁₆) refl

more-checkpoint₁₇ : Term (Step.Δ′ more-step₁₆)
more-checkpoint₁₇ = Step.next more-step₁₆

more-store₁₇ = Step.store-after more-step₁₆

more-step₁₇ : Step.OneStep more-store₁₇ more-checkpoint₁₇
more-step₁₇ =
  Step.from-just-step (step? more-store₁₇ more-checkpoint₁₇) refl

more-checkpoint₁₈ : Term (Step.Δ′ more-step₁₇)
more-checkpoint₁₈ = Step.next more-step₁₇

more-store₁₈ = Step.store-after more-step₁₇

more-step₁₈ : Step.OneStep more-store₁₈ more-checkpoint₁₈
more-step₁₈ =
  Step.from-just-step (step? more-store₁₈ more-checkpoint₁₈) refl

more-checkpoint₁₉ : Term (Step.Δ′ more-step₁₈)
more-checkpoint₁₉ = Step.next more-step₁₈

more-store₁₉ = Step.store-after more-step₁₈

more-step₁₉ : Step.OneStep more-store₁₉ more-checkpoint₁₉
more-step₁₉ =
  Step.from-just-step (step? more-store₁₉ more-checkpoint₁₉) refl

more-checkpoint₂₀ : Term (Step.Δ′ more-step₁₉)
more-checkpoint₂₀ = Step.next more-step₁₉

more-store₂₀ = Step.store-after more-step₁₉

more-step₂₀ : Step.OneStep more-store₂₀ more-checkpoint₂₀
more-step₂₀ =
  Step.from-just-step (step? more-store₂₀ more-checkpoint₂₀) refl

more-checkpoint₂₁ : Term (Step.Δ′ more-step₂₀)
more-checkpoint₂₁ = Step.next more-step₂₀

more-store₂₁ = Step.store-after more-step₂₀

less-step-term₀ : Term 0
less-step-term₀ = less-precise-compiled

less-step-store₀ = store-empty

less-step₀ : Step.OneStep less-step-store₀ less-step-term₀
less-step₀ =
  Step.from-just-step (step? less-step-store₀ less-step-term₀) refl

less-step-term₁ : Term (Step.Δ′ less-step₀)
less-step-term₁ = Step.next less-step₀

less-step-store₁ = Step.store-after less-step₀

less-step₁ : Step.OneStep less-step-store₁ less-step-term₁
less-step₁ =
  Step.from-just-step (step? less-step-store₁ less-step-term₁) refl

less-step-term₂ : Term (Step.Δ′ less-step₁)
less-step-term₂ = Step.next less-step₁

less-step-store₂ = Step.store-after less-step₁

less-step₂ : Step.OneStep less-step-store₂ less-step-term₂
less-step₂ =
  Step.from-just-step (step? less-step-store₂ less-step-term₂) refl

less-step-term₃ : Term (Step.Δ′ less-step₂)
less-step-term₃ = Step.next less-step₂

less-step-store₃ = Step.store-after less-step₂

less-step₃ : Step.OneStep less-step-store₃ less-step-term₃
less-step₃ =
  Step.from-just-step (step? less-step-store₃ less-step-term₃) refl

less-step-term₄ : Term (Step.Δ′ less-step₃)
less-step-term₄ = Step.next less-step₃

less-step-store₄ = Step.store-after less-step₃

less-step₄ : Step.OneStep less-step-store₄ less-step-term₄
less-step₄ =
  Step.from-just-step (step? less-step-store₄ less-step-term₄) refl

less-step-term₅ : Term (Step.Δ′ less-step₄)
less-step-term₅ = Step.next less-step₄

less-step-store₅ = Step.store-after less-step₄

less-step₅ : Step.OneStep less-step-store₅ less-step-term₅
less-step₅ =
  Step.from-just-step (step? less-step-store₅ less-step-term₅) refl

less-step-term₆ : Term (Step.Δ′ less-step₅)
less-step-term₆ = Step.next less-step₅

less-step-store₆ = Step.store-after less-step₅

less-step₆ : Step.OneStep less-step-store₆ less-step-term₆
less-step₆ =
  Step.from-just-step (step? less-step-store₆ less-step-term₆) refl

less-step-term₇ : Term (Step.Δ′ less-step₆)
less-step-term₇ = Step.next less-step₆

less-step-store₇ = Step.store-after less-step₆

less-step₇ : Step.OneStep less-step-store₇ less-step-term₇
less-step₇ =
  Step.from-just-step (step? less-step-store₇ less-step-term₇) refl

less-step-term₈ : Term (Step.Δ′ less-step₇)
less-step-term₈ = Step.next less-step₇

less-step-store₈ = Step.store-after less-step₇

less-step₈ : Step.OneStep less-step-store₈ less-step-term₈
less-step₈ =
  Step.from-just-step (step? less-step-store₈ less-step-term₈) refl

less-step-term₉ : Term (Step.Δ′ less-step₈)
less-step-term₉ = Step.next less-step₈

less-step-store₉ = Step.store-after less-step₈

less-step₉ : Step.OneStep less-step-store₉ less-step-term₉
less-step₉ =
  Step.from-just-step (step? less-step-store₉ less-step-term₉) refl

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

less-step₁₄ : Step.OneStep less-step-store₁₄ less-step-term₁₄
less-step₁₄ =
  Step.from-just-step (step? less-step-store₁₄ less-step-term₁₄) refl

less-step-term₁₅ : Term (Step.Δ′ less-step₁₄)
less-step-term₁₅ = Step.next less-step₁₄

less-step-store₁₅ = Step.store-after less-step₁₄

less-step₁₅ : Step.OneStep less-step-store₁₅ less-step-term₁₅
less-step₁₅ =
  Step.from-just-step (step? less-step-store₁₅ less-step-term₁₅) refl

less-step-term₁₆ : Term (Step.Δ′ less-step₁₅)
less-step-term₁₆ = Step.next less-step₁₅

less-step-store₁₆ = Step.store-after less-step₁₅

less-step₁₆ : Step.OneStep less-step-store₁₆ less-step-term₁₆
less-step₁₆ =
  Step.from-just-step (step? less-step-store₁₆ less-step-term₁₆) refl

less-step-term₁₇ : Term (Step.Δ′ less-step₁₆)
less-step-term₁₇ = Step.next less-step₁₆

less-step-store₁₇ = Step.store-after less-step₁₆

less-step₁₇ : Step.OneStep less-step-store₁₇ less-step-term₁₇
less-step₁₇ =
  Step.from-just-step (step? less-step-store₁₇ less-step-term₁₇) refl

less-step-term₁₈ : Term (Step.Δ′ less-step₁₇)
less-step-term₁₈ = Step.next less-step₁₇

less-step-store₁₈ = Step.store-after less-step₁₇

less-step₁₈ : Step.OneStep less-step-store₁₈ less-step-term₁₈
less-step₁₈ =
  Step.from-just-step (step? less-step-store₁₈ less-step-term₁₈) refl

less-step-term₁₉ : Term (Step.Δ′ less-step₁₈)
less-step-term₁₉ = Step.next less-step₁₈

less-step-store₁₉ = Step.store-after less-step₁₈

less-step₁₉ : Step.OneStep less-step-store₁₉ less-step-term₁₉
less-step₁₉ =
  Step.from-just-step (step? less-step-store₁₉ less-step-term₁₉) refl

less-step-term₂₀ : Term (Step.Δ′ less-step₁₉)
less-step-term₂₀ = Step.next less-step₁₉

less-step-store₂₀ = Step.store-after less-step₁₉

less-step₂₀ : Step.OneStep less-step-store₂₀ less-step-term₂₀
less-step₂₀ =
  Step.from-just-step (step? less-step-store₂₀ less-step-term₂₀) refl

less-step-term₂₁ : Term (Step.Δ′ less-step₂₀)
less-step-term₂₁ = Step.next less-step₂₀

less-step-store₂₁ = Step.store-after less-step₂₀

less-step₂₁ : Step.OneStep less-step-store₂₁ less-step-term₂₁
less-step₂₁ =
  Step.from-just-step (step? less-step-store₂₁ less-step-term₂₁) refl

less-step-term₂₂ : Term (Step.Δ′ less-step₂₁)
less-step-term₂₂ = Step.next less-step₂₁

less-step-store₂₂ = Step.store-after less-step₂₁

less-step₂₂ : Step.OneStep less-step-store₂₂ less-step-term₂₂
less-step₂₂ =
  Step.from-just-step (step? less-step-store₂₂ less-step-term₂₂) refl

less-step-term₂₃ : Term (Step.Δ′ less-step₂₂)
less-step-term₂₃ = Step.next less-step₂₂

less-step-store₂₃ = Step.store-after less-step₂₂

less-step₂₃ : Step.OneStep less-step-store₂₃ less-step-term₂₃
less-step₂₃ =
  Step.from-just-step (step? less-step-store₂₃ less-step-term₂₃) refl

less-step-term₂₄ : Term (Step.Δ′ less-step₂₃)
less-step-term₂₄ = Step.next less-step₂₃

less-step-store₂₄ = Step.store-after less-step₂₃

less-step₂₄ : Step.OneStep less-step-store₂₄ less-step-term₂₄
less-step₂₄ =
  Step.from-just-step (step? less-step-store₂₄ less-step-term₂₄) refl

less-step-term₂₅ : Term (Step.Δ′ less-step₂₄)
less-step-term₂₅ = Step.next less-step₂₄

less-step-store₂₅ = Step.store-after less-step₂₄

less-step₂₅ : Step.OneStep less-step-store₂₅ less-step-term₂₅
less-step₂₅ =
  Step.from-just-step (step? less-step-store₂₅ less-step-term₂₅) refl

less-step-term₂₆ : Term (Step.Δ′ less-step₂₅)
less-step-term₂₆ = Step.next less-step₂₅

less-step-store₂₆ = Step.store-after less-step₂₅

less-step₂₆ : Step.OneStep less-step-store₂₆ less-step-term₂₆
less-step₂₆ =
  Step.from-just-step (step? less-step-store₂₆ less-step-term₂₆) refl

less-step-term₂₇ : Term (Step.Δ′ less-step₂₆)
less-step-term₂₇ = Step.next less-step₂₆

less-step-store₂₇ = Step.store-after less-step₂₆

more-step₂₁ : Step.OneStep more-store₂₁ more-checkpoint₂₁
more-step₂₁ =
  Step.from-just-step (step? more-store₂₁ more-checkpoint₂₁) refl

more-checkpoint₂₂ : Term (Step.Δ′ more-step₂₁)
more-checkpoint₂₂ = Step.next more-step₂₁

more-store₂₂ = Step.store-after more-step₂₁

more-step₂₂ : Step.OneStep more-store₂₂ more-checkpoint₂₂
more-step₂₂ =
  Step.from-just-step (step? more-store₂₂ more-checkpoint₂₂) refl

more-checkpoint₂₃ : Term (Step.Δ′ more-step₂₂)
more-checkpoint₂₃ = Step.next more-step₂₂

more-store₂₃ = Step.store-after more-step₂₂

more-step₂₃ : Step.OneStep more-store₂₃ more-checkpoint₂₃
more-step₂₃ =
  Step.from-just-step (step? more-store₂₃ more-checkpoint₂₃) refl

more-checkpoint₂₄ : Term (Step.Δ′ more-step₂₃)
more-checkpoint₂₄ = Step.next more-step₂₃

more-store₂₄ = Step.store-after more-step₂₃

more-step₂₄ : Step.OneStep more-store₂₄ more-checkpoint₂₄
more-step₂₄ =
  Step.from-just-step (step? more-store₂₄ more-checkpoint₂₄) refl

more-checkpoint₂₅ : Term (Step.Δ′ more-step₂₄)
more-checkpoint₂₅ = Step.next more-step₂₄

more-store₂₅ = Step.store-after more-step₂₄

less-step₂₇ : Step.OneStep less-step-store₂₇ less-step-term₂₇
less-step₂₇ =
  Step.from-just-step (step? less-step-store₂₇ less-step-term₂₇) refl

less-step-term₂₈ : Term (Step.Δ′ less-step₂₇)
less-step-term₂₈ = Step.next less-step₂₇

less-step-store₂₈ = Step.store-after less-step₂₇

less-step₂₈ : Step.OneStep less-step-store₂₈ less-step-term₂₈
less-step₂₈ =
  Step.from-just-step (step? less-step-store₂₈ less-step-term₂₈) refl

less-step-term₂₉ : Term (Step.Δ′ less-step₂₈)
less-step-term₂₉ = Step.next less-step₂₈

less-step-store₂₉ = Step.store-after less-step₂₈

less-step₂₉ : Step.OneStep less-step-store₂₉ less-step-term₂₉
less-step₂₉ =
  Step.from-just-step (step? less-step-store₂₉ less-step-term₂₉) refl

less-step-term₃₀ : Term (Step.Δ′ less-step₂₉)
less-step-term₃₀ = Step.next less-step₂₉

less-step-store₃₀ = Step.store-after less-step₂₉

less-step₃₀ : Step.OneStep less-step-store₃₀ less-step-term₃₀
less-step₃₀ =
  Step.from-just-step (step? less-step-store₃₀ less-step-term₃₀) refl

less-step-term₃₁ : Term (Step.Δ′ less-step₃₀)
less-step-term₃₁ = Step.next less-step₃₀

less-step-store₃₁ = Step.store-after less-step₃₀


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

less-checkpoint₄ : Term (Step.Δ′ less-step₃)
less-checkpoint₄ = less-step-term₄

less-checkpoint₅ : Term (Step.Δ′ less-step₄)
less-checkpoint₅ = less-step-term₅

less-checkpoint₆ : Term (Step.Δ′ less-step₆)
less-checkpoint₆ = less-step-term₇

less-checkpoint₇ : Term (Step.Δ′ less-step₆)
less-checkpoint₇ = less-step-term₇

less-checkpoint₈ : Term (Step.Δ′ less-step₇)
less-checkpoint₈ = less-step-term₈

less-checkpoint₉ : Term (Step.Δ′ less-step₈)
less-checkpoint₉ = less-step-term₉

less-checkpoint₁₀ : Term (Step.Δ′ less-step₁₀)
less-checkpoint₁₀ = less-step-term₁₁

less-checkpoint₁₁ : Term (Step.Δ′ less-step₁₄)
less-checkpoint₁₁ = less-step-term₁₅

less-checkpoint₁₂ : Term (Step.Δ′ less-step₁₄)
less-checkpoint₁₂ = less-step-term₁₅

less-checkpoint₁₃ : Term (Step.Δ′ less-step₁₅)
less-checkpoint₁₃ = less-step-term₁₆

less-checkpoint₁₄ : Term (Step.Δ′ less-step₁₆)
less-checkpoint₁₄ = less-step-term₁₇

less-checkpoint₁₅ : Term (Step.Δ′ less-step₁₇)
less-checkpoint₁₅ = less-step-term₁₈

less-checkpoint₁₆ : Term (Step.Δ′ less-step₁₈)
less-checkpoint₁₆ = less-step-term₁₉

less-checkpoint₁₇ : Term (Step.Δ′ less-step₁₉)
less-checkpoint₁₇ = less-step-term₂₀

less-checkpoint₁₈ : Term (Step.Δ′ less-step₂₁)
less-checkpoint₁₈ = less-step-term₂₂

less-checkpoint₁₉ : Term (Step.Δ′ less-step₂₂)
less-checkpoint₁₉ = less-step-term₂₃

less-checkpoint₂₀ : Term (Step.Δ′ less-step₂₃)
less-checkpoint₂₀ = less-step-term₂₄

less-checkpoint₂₁ : Term (Step.Δ′ less-step₂₄)
less-checkpoint₂₁ = less-step-term₂₅

less-checkpoint₂₂ : Term (Step.Δ′ less-step₂₆)
less-checkpoint₂₂ = less-step-term₂₇

less-checkpoint₂₃ : Term (Step.Δ′ less-step₂₇)
less-checkpoint₂₃ = less-step-term₂₈

less-checkpoint₂₄ : Term (Step.Δ′ less-step₂₉)
less-checkpoint₂₄ = less-step-term₃₀

less-checkpoint₂₅ : Term (Step.Δ′ less-step₃₀)
less-checkpoint₂₅ = less-step-term₃₁

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
  less-checkpoint₃ —↠[ keep ∷ [] ] less-checkpoint₄
less-checkpoint₃↠₄ =
  less-checkpoint₃
  —→[ keep ]⟨ Step.reduction less-step₃ ⟩
  less-checkpoint₄
  ∎[]

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
  —→[ keep ]⟨ Step.reduction less-step₄ ⟩
  less-checkpoint₅
  ∎[]

more-checkpoint₅↠₆ :
  more-checkpoint₅ —↠[ keep ∷ [] ] more-checkpoint₆
more-checkpoint₅↠₆ =
  more-checkpoint₅
  —→[ keep ]⟨ Step.reduction more-step₅ ⟩
  more-checkpoint₆ ∎[]

less-checkpoint₅↠₆ :
  less-checkpoint₅ —↠[ keep ∷ keep ∷ [] ] less-checkpoint₆
less-checkpoint₅↠₆ =
  less-checkpoint₅
  —→[ keep ]⟨ Step.reduction less-step₅ ⟩
  less-step-term₆
  —→[ keep ]⟨ Step.reduction less-step₆ ⟩
  less-checkpoint₆
  ∎[]

more-checkpoint₆↠₇ :
  more-checkpoint₆ —↠[ keep ∷ [] ] more-checkpoint₇
more-checkpoint₆↠₇ =
  more-checkpoint₆
  —→[ keep ]⟨ Step.reduction more-step₆ ⟩
  more-checkpoint₇ ∎[]

less-checkpoint₆↠₇ :
  less-checkpoint₆ —↠[ [] ] less-checkpoint₇
less-checkpoint₆↠₇ =
  less-checkpoint₇ ∎[]

more-checkpoint₇↠₈ :
  more-checkpoint₇ —↠[ keep ∷ [] ] more-checkpoint₈
more-checkpoint₇↠₈ =
  more-checkpoint₇
  —→[ keep ]⟨ Step.reduction more-step₇ ⟩
  more-checkpoint₈ ∎[]

less-checkpoint₇↠₈ :
  less-checkpoint₇ —↠[ keep ∷ [] ] less-checkpoint₈
less-checkpoint₇↠₈ =
  less-checkpoint₇
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
  less-checkpoint₁₀ —↠[ keep ∷ keep ∷ keep ∷ keep ∷ [] ] less-checkpoint₁₁
less-checkpoint₁₀↠₁₁ =
  less-checkpoint₁₀
  —→[ keep ]⟨ Step.reduction less-step₁₁ ⟩
  less-step-term₁₂
  —→[ keep ]⟨ Step.reduction less-step₁₂ ⟩
  less-step-term₁₃
  —→[ keep ]⟨ Step.reduction less-step₁₃ ⟩
  less-step-term₁₄
  —→[ keep ]⟨ Step.reduction less-step₁₄ ⟩
  less-checkpoint₁₁
  ∎[]

more-checkpoint₁₁↠₁₂ :
  more-checkpoint₁₁ —↠[ keep ∷ [] ] more-checkpoint₁₂
more-checkpoint₁₁↠₁₂ =
  more-checkpoint₁₁
  —→[ keep ]⟨ Step.reduction more-step₁₁ ⟩
  more-checkpoint₁₂ ∎[]

less-checkpoint₁₁↠₁₂ :
  less-checkpoint₁₁ —↠[ [] ] less-checkpoint₁₂
less-checkpoint₁₁↠₁₂ =
  less-checkpoint₁₂ ∎[]

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
  —→[ keep ]⟨ Step.reduction less-step₁₅ ⟩
  less-checkpoint₁₃
  ∎[]

more-checkpoint₁₃↠₁₄ :
  more-checkpoint₁₃ —↠[ keep ∷ [] ] more-checkpoint₁₄
more-checkpoint₁₃↠₁₄ =
  more-checkpoint₁₃
  —→[ keep ]⟨ Step.reduction more-step₁₃ ⟩
  more-checkpoint₁₄ ∎[]

less-checkpoint₁₃↠₁₄ :
  less-checkpoint₁₃ —↠[ keep ∷ [] ] less-checkpoint₁₄
less-checkpoint₁₃↠₁₄ =
  less-checkpoint₁₃
  —→[ keep ]⟨ Step.reduction less-step₁₆ ⟩
  less-checkpoint₁₄
  ∎[]

more-checkpoint₁₄↠₁₅ :
  more-checkpoint₁₄ —↠[ keep ∷ [] ] more-checkpoint₁₅
more-checkpoint₁₄↠₁₅ =
  more-checkpoint₁₄
  —→[ keep ]⟨ Step.reduction more-step₁₄ ⟩
  more-checkpoint₁₅ ∎[]

less-checkpoint₁₄↠₁₅ :
  less-checkpoint₁₄ —↠[ keep ∷ [] ] less-checkpoint₁₅
less-checkpoint₁₄↠₁₅ =
  less-checkpoint₁₄
  —→[ keep ]⟨ Step.reduction less-step₁₇ ⟩
  less-checkpoint₁₅
  ∎[]

more-checkpoint₁₅↠₁₆ :
  more-checkpoint₁₅ —↠[ keep ∷ [] ] more-checkpoint₁₆
more-checkpoint₁₅↠₁₆ =
  more-checkpoint₁₅
  —→[ keep ]⟨ Step.reduction more-step₁₅ ⟩
  more-checkpoint₁₆ ∎[]

less-checkpoint₁₅↠₁₆ :
  less-checkpoint₁₅ —↠[ keep ∷ [] ] less-checkpoint₁₆
less-checkpoint₁₅↠₁₆ =
  less-checkpoint₁₅
  —→[ keep ]⟨ Step.reduction less-step₁₈ ⟩
  less-checkpoint₁₆
  ∎[]

more-checkpoint₁₆↠₁₇ :
  more-checkpoint₁₆ —↠[ keep ∷ [] ] more-checkpoint₁₇
more-checkpoint₁₆↠₁₇ =
  more-checkpoint₁₆
  —→[ keep ]⟨ Step.reduction more-step₁₆ ⟩
  more-checkpoint₁₇ ∎[]

less-checkpoint₁₆↠₁₇ :
  less-checkpoint₁₆ —↠[ keep ∷ [] ] less-checkpoint₁₇
less-checkpoint₁₆↠₁₇ =
  less-checkpoint₁₆
  —→[ keep ]⟨ Step.reduction less-step₁₉ ⟩
  less-checkpoint₁₇
  ∎[]

more-checkpoint₁₇↠₁₈ :
  more-checkpoint₁₇ —↠[ keep ∷ [] ] more-checkpoint₁₈
more-checkpoint₁₇↠₁₈ =
  more-checkpoint₁₇
  —→[ keep ]⟨ Step.reduction more-step₁₇ ⟩
  more-checkpoint₁₈ ∎[]

less-checkpoint₁₇↠₁₈ :
  less-checkpoint₁₇ —↠[ keep ∷ keep ∷ [] ] less-checkpoint₁₈
less-checkpoint₁₇↠₁₈ =
  less-checkpoint₁₇
  —→[ keep ]⟨ Step.reduction less-step₂₀ ⟩
  less-step-term₂₁
  —→[ keep ]⟨ Step.reduction less-step₂₁ ⟩
  less-checkpoint₁₈
  ∎[]

more-checkpoint₁₈↠₁₉ :
  more-checkpoint₁₈ —↠[ keep ∷ [] ] more-checkpoint₁₉
more-checkpoint₁₈↠₁₉ =
  more-checkpoint₁₈
  —→[ keep ]⟨ Step.reduction more-step₁₈ ⟩
  more-checkpoint₁₉ ∎[]

less-checkpoint₁₈↠₁₉ :
  less-checkpoint₁₈ —↠[ keep ∷ [] ] less-checkpoint₁₉
less-checkpoint₁₈↠₁₉ =
  less-checkpoint₁₈
  —→[ keep ]⟨ Step.reduction less-step₂₂ ⟩
  less-checkpoint₁₉
  ∎[]

more-checkpoint₁₉↠₂₀ :
  more-checkpoint₁₉ —↠[ keep ∷ [] ] more-checkpoint₂₀
more-checkpoint₁₉↠₂₀ =
  more-checkpoint₁₉
  —→[ keep ]⟨ Step.reduction more-step₁₉ ⟩
  more-checkpoint₂₀ ∎[]

less-checkpoint₁₉↠₂₀ :
  less-checkpoint₁₉ —↠[ keep ∷ [] ] less-checkpoint₂₀
less-checkpoint₁₉↠₂₀ =
  less-checkpoint₁₉
  —→[ keep ]⟨ Step.reduction less-step₂₃ ⟩
  less-checkpoint₂₀
  ∎[]

more-checkpoint₂₀↠₂₁ :
  more-checkpoint₂₀ —↠[ keep ∷ [] ] more-checkpoint₂₁
more-checkpoint₂₀↠₂₁ =
  more-checkpoint₂₀
  —→[ keep ]⟨ Step.reduction more-step₂₀ ⟩
  more-checkpoint₂₁ ∎[]

less-checkpoint₂₀↠₂₁ :
  less-checkpoint₂₀ —↠[ keep ∷ [] ] less-checkpoint₂₁
less-checkpoint₂₀↠₂₁ =
  less-checkpoint₂₀
  —→[ keep ]⟨ Step.reduction less-step₂₄ ⟩
  less-checkpoint₂₁
  ∎[]

more-checkpoint₂₁↠₂₂ :
  more-checkpoint₂₁ —↠[ keep ∷ [] ] more-checkpoint₂₂
more-checkpoint₂₁↠₂₂ =
  more-checkpoint₂₁
  —→[ keep ]⟨ Step.reduction more-step₂₁ ⟩
  more-checkpoint₂₂ ∎[]

less-checkpoint₂₁↠₂₂ :
  less-checkpoint₂₁ —↠[ keep ∷ keep ∷ [] ] less-checkpoint₂₂
less-checkpoint₂₁↠₂₂ =
  less-checkpoint₂₁
  —→[ keep ]⟨ Step.reduction less-step₂₅ ⟩
  less-step-term₂₆
  —→[ keep ]⟨ Step.reduction less-step₂₆ ⟩
  less-checkpoint₂₂
  ∎[]

more-checkpoint₂₂↠₂₃ :
  more-checkpoint₂₂ —↠[ keep ∷ [] ] more-checkpoint₂₃
more-checkpoint₂₂↠₂₃ =
  more-checkpoint₂₂
  —→[ keep ]⟨ Step.reduction more-step₂₂ ⟩
  more-checkpoint₂₃ ∎[]

less-checkpoint₂₂↠₂₃ :
  less-checkpoint₂₂ —↠[ keep ∷ [] ] less-checkpoint₂₃
less-checkpoint₂₂↠₂₃ =
  less-checkpoint₂₂
  —→[ keep ]⟨ Step.reduction less-step₂₇ ⟩
  less-checkpoint₂₃
  ∎[]

more-checkpoint₂₃↠₂₄ :
  more-checkpoint₂₃ —↠[ keep ∷ [] ] more-checkpoint₂₄
more-checkpoint₂₃↠₂₄ =
  more-checkpoint₂₃
  —→[ keep ]⟨ Step.reduction more-step₂₃ ⟩
  more-checkpoint₂₄ ∎[]

less-checkpoint₂₃↠₂₄ :
  less-checkpoint₂₃ —↠[ keep ∷ keep ∷ [] ] less-checkpoint₂₄
less-checkpoint₂₃↠₂₄ =
  less-checkpoint₂₃
  —→[ keep ]⟨ Step.reduction less-step₂₈ ⟩
  less-step-term₂₉
  —→[ keep ]⟨ Step.reduction less-step₂₉ ⟩
  less-checkpoint₂₄
  ∎[]

more-checkpoint₂₄↠₂₅ :
  more-checkpoint₂₄ —↠[ keep ∷ [] ] more-checkpoint₂₅
more-checkpoint₂₄↠₂₅ =
  more-checkpoint₂₄
  —→[ keep ]⟨ Step.reduction more-step₂₄ ⟩
  more-checkpoint₂₅ ∎[]

less-checkpoint₂₄↠₂₅ :
  less-checkpoint₂₄ —↠[ keep ∷ [] ] less-checkpoint₂₅
less-checkpoint₂₄↠₂₅ =
  less-checkpoint₂₄
  —→[ keep ]⟨ Step.reduction less-step₃₀ ⟩
  less-checkpoint₂₅
  ∎[]

more-final : more-checkpoint₂₅ ≡ C.$ (κℕ 42)
more-final = refl

less-final : less-checkpoint₂₅ ≡ C.$ (κℕ 42)
less-final = refl


------------------------------------------------------------------------
-- Initial cast-term imprecision
------------------------------------------------------------------------

initial-argument-imprecision :
  emptyᶜ CTI.⊢²
    C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ id {μ = idᶜ} (‵ `ℕ) ! ⟩))
    ⊑ C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ id {μ = idᶜ} ★ ⟩)) ∶ ℕ⇒★⊑★⇒★
initial-argument-imprecision =
  CTI.ƛ⊑ƛ²
    (CTI.·⊑·²
      (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
        (CTI.x⊑x² {p = I.★⊑★} Z Z))
      (CTI.cast⊑cast²
        (id {μ = idᶜ} (‵ `ℕ) !)
        (id {μ = idᶜ} ★)
        (CTI.x⊑x² {p = I.ι⊑★} Z Z)
        I.★⊑★))

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
        (CTI.·⊑·²
          (CTI.•⊑²
            ∀higher-X⊑higher-dynamic
            (CTI.·⊑·²
              (CTI.ƛ⊑ƛ²
                (CTI.x⊑x²
                  {p = ∀higher-X⊑higher-dynamic} Z Z))
              (CTI.cast⊑cast²
                (symᶜ ∀higher-X∼∀higher-X)
                (symᶜ higher-dynamic∼∀higher-X)
                (CTI.Λ⊑Λ²
                  (C.ƛ (C.` 0))
                  (C.ƛ (C.` 0))
                  (CTI.ƛ⊑ƛ²
                    {pA = X⇒★⊑X⇒★}
                    {pB = X⇒★⊑X⇒★}
                    (CTI.x⊑x² {p = X⇒★⊑X⇒★} Z Z))
                  ∀higher-X⊑∀higher-X)
                ∀higher-X⊑higher-dynamic))
            I.ι⊑★
            higher-ℕ⊑higher-dynamic)
          (CTI.cast⊑cast²
            (symᶜ (id (‵ `ℕ) ↦ id ★))
            (symᶜ (id ★ ↦ id ★))
            initial-argument-imprecision
            ℕ⇒★⊑★⇒★))
        (CTI.cast⊑cast²
          (symᶜ (id (‵ `ℕ)))
          (symᶜ (symᶜ nat-consistent-star))
          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
          I.ι⊑★))
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₀-ladder : String
checkpoint₀-ladder = impLadderDefault checkpoint₀-imprecision


------------------------------------------------------------------------
-- Checkpoint 1: target beta and alpha higher-order reveals
------------------------------------------------------------------------

checkpoint₁-beta-higher-reveal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↑[ Fin.zero ⦂ ＇ (Fin.suc Fin.zero) ]
      ((unseal Fin.zero (＇ (Fin.suc Fin.zero)) Conv.↦↓
          Conv.id↓ ★) Conv.↦↑
        (seal Fin.zero (＇ (Fin.suc Fin.zero)) Conv.↦↑
          Conv.id↑ ★))
checkpoint₁-beta-higher-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-⇒
      (Conv.⊢↑-unseal TIR.checkpoint₁-beta-member)
      (Conv.⊢↓-id-star TIR.checkpoint₁-beta-member))
    (Conv.⊢↑-⇒
      (Conv.⊢↓-seal TIR.checkpoint₁-beta-member)
      (Conv.⊢↑-id-star TIR.checkpoint₁-beta-member))

checkpoint₁-alpha-higher-reveal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↑[ Fin.suc Fin.zero ⦂ ★ ]
      ((unseal (Fin.suc Fin.zero) ★ Conv.↦↓ Conv.id↓ ★)
        Conv.↦↑
        (seal (Fin.suc Fin.zero) ★ Conv.↦↑ Conv.id↑ ★))
checkpoint₁-alpha-higher-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-⇒
      (Conv.⊢↑-unseal TIR.checkpoint₁-alpha-member)
      (Conv.⊢↓-id-star TIR.checkpoint₁-alpha-member))
    (Conv.⊢↑-⇒
      (Conv.⊢↓-seal TIR.checkpoint₁-alpha-member)
      (Conv.⊢↑-id-star TIR.checkpoint₁-alpha-member))

checkpoint₁-beta-higher-active :
  revealGeneratorPosition checkpoint₁-beta-higher-reveal⊢
    ≢ generator-absent
checkpoint₁-beta-higher-active ()

checkpoint₁-alpha-higher-active :
  revealGeneratorPosition checkpoint₁-alpha-higher-reveal⊢
    ≢ generator-absent
checkpoint₁-alpha-higher-active ()

checkpoint₁-target-function : Term 2
checkpoint₁-target-function = C.ƛ (C.` 0)

checkpoint₁-target-beta-reveal : Term 2
checkpoint₁-target-beta-reveal =
  checkpoint₁-target-function C.↑
    ((unseal Fin.zero (＇ (Fin.suc Fin.zero)) Conv.↦↓
        Conv.id↓ ★) Conv.↦↑
      (seal Fin.zero (＇ (Fin.suc Fin.zero)) Conv.↦↑
        Conv.id↑ ★))

checkpoint₁-target-payload : Term 2
checkpoint₁-target-payload =
  checkpoint₁-target-beta-reveal C.↑
    ((unseal (Fin.suc Fin.zero) ★ Conv.↦↓ Conv.id↓ ★)
      Conv.↦↑
      (seal (Fin.suc Fin.zero) ★ Conv.↦↑ Conv.id↑ ★))

checkpoint₁-target-function-⊢ :
  ((TIR.base-context ,ˢ ★) ,ˢ ＇ Fin.zero) ⊢
    checkpoint₁-target-function
    ⦂ ((＇ Fin.zero ⇒ ★) ⇒ (＇ Fin.zero ⇒ ★))
checkpoint₁-target-function-⊢ = C.⊢ƛ (C.⊢` Z)

checkpoint₁-target-beta-reveal-⊢ :
  ((TIR.base-context ,ˢ ★) ,ˢ ＇ Fin.zero) ⊢
    checkpoint₁-target-beta-reveal
    ⦂ ((＇ (Fin.suc Fin.zero) ⇒ ★) ⇒
       (＇ (Fin.suc Fin.zero) ⇒ ★))
checkpoint₁-target-beta-reveal-⊢ =
  C.⊢reveal checkpoint₁-beta-higher-reveal⊢
    checkpoint₁-target-function-⊢

checkpoint₁-target-payload-⊢ :
  ((TIR.base-context ,ˢ ★) ,ˢ ＇ Fin.zero) ⊢
    checkpoint₁-target-payload ⦂ higher-dynamic
checkpoint₁-target-payload-⊢ =
  C.⊢reveal checkpoint₁-alpha-higher-reveal⊢
    checkpoint₁-target-beta-reveal-⊢

checkpoint₁-function-imprecision :
  TIR.checkpoint₁-beta-current CTI.⊢²
    C.ƛ (C.` 0) ⊑ C.ƛ (C.` 0)
    ∶ I.⇒⊑⇒
        (I.⇒⊑⇒ (I.X⊑X {X = Fin.suc Fin.zero}) I.★⊑★)
        (I.⇒⊑⇒ (I.X⊑X {X = Fin.suc Fin.zero}) I.★⊑★)
checkpoint₁-function-imprecision =
  CTI.ƛ⊑ƛ²
    {pA = I.⇒⊑⇒
      (I.X⊑X {X = Fin.suc Fin.zero}) I.★⊑★}
    {pB = I.⇒⊑⇒
      (I.X⊑X {X = Fin.suc Fin.zero}) I.★⊑★}
    (CTI.x⊑x²
      {p = I.⇒⊑⇒
        (I.X⊑X {X = Fin.suc Fin.zero}) I.★⊑★} Z Z)

checkpoint₁-reveals-imprecision :
  TIR.checkpoint₁-outside-world CTI.⊢²
    C.ƛ (C.` 0) ⊑ checkpoint₁-target-payload
    ∶ higher-X⊑higher-dynamic
checkpoint₁-reveals-imprecision =
  CTI.⊑reveal-rebase²
    {M′ = checkpoint₁-target-beta-reveal}
    checkpoint₁-alpha-higher-reveal⊢
    (source-rebase-now TIR.checkpoint₁-alpha-ok
      TIR.checkpoint₁-alpha-representation)
    (CTI.⊑reveal-rebase²
      {M′ = checkpoint₁-target-function}
      checkpoint₁-beta-higher-reveal⊢
      (source-rebase-now TIR.checkpoint₁-beta-ok
        TIR.checkpoint₁-beta-representation)
      checkpoint₁-function-imprecision
      (I.⇒⊑⇒
        (I.⇒⊑⇒
          (I.X⊑X {X = Fin.suc (Fin.suc Fin.zero)}) I.★⊑★)
        (I.⇒⊑⇒
          (I.X⊑X {X = Fin.suc (Fin.suc Fin.zero)}) I.★⊑★)))
    higher-X⊑higher-dynamic

checkpoint₁-poly-imprecision :
  TIR.checkpoint₁-world CTI.⊢²
    C.Λ (C.ƛ (C.` 0)) ⊑ checkpoint₁-target-payload
    ∶ ∀higher-X⊑higher-dynamic
checkpoint₁-poly-imprecision =
  CTI.Λ⊑² nonvar-fun X∈higher-X
    (C.ƛ (C.` 0)) checkpoint₁-target-payload-⊢
    checkpoint₁-reveals-imprecision
    ∀higher-X⊑higher-dynamic

checkpoint₁-target-id-higher :
  applyEnv (bind (＇ Fin.zero))
    (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})) ⊢
    higher-dynamic ∼ higher-dynamic
checkpoint₁-target-id-higher =
  (id ★ ↦ id ★) ↦ (id ★ ↦ id ★)

checkpoint₁-target-argument-id-star :
  renameEnv∼ (Consistency.skip id↪ᵗ)
    (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})) ⊢ ★ ∼ ★
checkpoint₁-target-argument-id-star = id ★

checkpoint₁-target-argument-id-function :
  renameEnv∼ (Consistency.skip id↪ᵗ)
    (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})) ⊢
    dynamic-function ∼ dynamic-function
checkpoint₁-target-argument-id-function =
  id ★ ↦ id ★

checkpoint₁-argument-imprecision :
  TIR.checkpoint₁-world CTI.⊢²
    ((C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ id {μ = idᶜ} (‵ `ℕ) ! ⟩))) C.⟨
        id {μ = flipᵐ idᶜ} (‵ `ℕ) ↦
        id {μ = idᶜ} ★ ⟩)
    ⊑ ((C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ checkpoint₁-target-argument-id-star ⟩))) C.⟨
        checkpoint₁-target-argument-id-function ⟩)
    ∶ ℕ⇒★⊑★⇒★
checkpoint₁-argument-imprecision =
  CTI.cast⊑cast²
    (id {μ = flipᵐ idᶜ} (‵ `ℕ) ↦ id {μ = idᶜ} ★)
    checkpoint₁-target-argument-id-function
    (CTI.ƛ⊑ƛ²
      {pA = I.ι⊑★}
      {pB = I.★⊑★}
      (CTI.·⊑·²
        (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
          (CTI.x⊑x² {p = I.★⊑★} Z Z))
        (CTI.cast⊑cast²
          (id {μ = idᶜ} (‵ `ℕ) !)
          checkpoint₁-target-argument-id-star
          (CTI.x⊑x² {p = I.ι⊑★} Z Z)
          I.★⊑★)))
    ℕ⇒★⊑★⇒★

checkpoint₁-imprecision :
  TIR.checkpoint₁-world CTI.⊢²
    more-checkpoint₁ ⊑ less-checkpoint₁ ∶ I.ι⊑ι
checkpoint₁-imprecision
  rewrite more-argument-compiled-shape
        | less-argument-compiled-shape =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (symᶜ nat-consistent-star)
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★)
          (symᶜ nat-consistent-star)))
      (CTI.·⊑·²
        (CTI.·⊑·²
          (CTI.•⊑²
            ∀higher-X⊑higher-dynamic
            (CTI.cast⊑cast²
              (symᶜ ∀higher-X∼∀higher-X)
              checkpoint₁-target-id-higher
              checkpoint₁-poly-imprecision
              ∀higher-X⊑higher-dynamic)
            I.ι⊑★
            higher-ℕ⊑higher-dynamic)
          checkpoint₁-argument-imprecision)
        (CTI.cast⊑cast²
          (symᶜ (id (‵ `ℕ)))
          (id (‵ `ℕ) !)
          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
          I.ι⊑★))
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁-ladder : String
checkpoint₁-ladder = impLadderDefault checkpoint₁-imprecision


------------------------------------------------------------------------
-- Checkpoint 2: the source universal identity cast has distributed
------------------------------------------------------------------------

checkpoint₂-imprecision :
  TIR.checkpoint₁-world CTI.⊢²
    more-checkpoint₂ ⊑ less-checkpoint₂ ∶ I.ι⊑ι
checkpoint₂-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      (symᶜ nat-consistent-star)
      (applyConsistency (bind (＇ Fin.zero))
        (applyConsistency (bind ★)
          (symᶜ nat-consistent-star)))
      (CTI.·⊑·²
        (CTI.·⊑·²
          (CTI.cast⊑cast²
            ((id (‵ `ℕ) ↦ id ★) ↦ (id (‵ `ℕ) ↦ id ★))
            checkpoint₁-target-id-higher
            (CTI.•⊑²
              ∀higher-X⊑higher-dynamic
              checkpoint₁-poly-imprecision
              I.ι⊑★
              higher-ℕ⊑higher-dynamic)
            higher-ℕ⊑higher-dynamic)
          checkpoint₁-argument-imprecision)
      (CTI.cast⊑cast²
        (symᶜ (id (‵ `ℕ)))
        (id (‵ `ℕ) !)
        (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
        I.ι⊑★))
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₂-ladder : String
checkpoint₂-ladder = impLadderDefault checkpoint₂-imprecision


------------------------------------------------------------------------
-- Checkpoint 3: source allocation aligns with target alpha
------------------------------------------------------------------------

checkpoint₃-source-higher-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    ((unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★) Conv.↦↑
      (seal Fin.zero ℕᵗ Conv.↦↑ Conv.id↑ ★))
checkpoint₃-source-higher-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-⇒
      (Conv.⊢↑-unseal TIR.checkpoint₃-source-member)
      (Conv.⊢↓-id-star TIR.checkpoint₃-source-member))
    (Conv.⊢↑-⇒
      (Conv.⊢↓-seal TIR.checkpoint₃-source-member)
      (Conv.⊢↑-id-star TIR.checkpoint₃-source-member))

checkpoint₃-source-higher-active :
  revealGeneratorPosition checkpoint₃-source-higher-reveal⊢
    ≢ generator-absent
checkpoint₃-source-higher-active ()

checkpoint₃-source-id-higher :
  extᵐ (idᶜ {Δ = 0}) ⊢
    ((ℕᵗ ⇒ ★) ⇒ (ℕᵗ ⇒ ★)) ∼
    ((ℕᵗ ⇒ ★) ⇒ (ℕᵗ ⇒ ★))
checkpoint₃-source-id-higher =
  (id (‵ `ℕ) ↦ id ★) ↦ (id (‵ `ℕ) ↦ id ★)

checkpoint₃-variable-imprecision :
  (＇ Fin.zero) ⊑ᵀ⟨ TIR.checkpoint₃-beta-current ⟩
    (＇ Fin.zero)
checkpoint₃-variable-imprecision = I.X⊑X

checkpoint₃-alpha-variable-imprecision :
  (＇ Fin.zero) ⊑ᵀ⟨ TIR.checkpoint₃-world ⟩
    (＇ (Fin.suc Fin.zero))
checkpoint₃-alpha-variable-imprecision = I.X⊑X

checkpoint₃-function-imprecision :
  TIR.checkpoint₃-beta-current CTI.⊢²
    C.ƛ (C.` 0) ⊑ C.ƛ (C.` 0)
    ∶ I.⇒⊑⇒
        (I.⇒⊑⇒ checkpoint₃-variable-imprecision I.★⊑★)
        (I.⇒⊑⇒ checkpoint₃-variable-imprecision I.★⊑★)
checkpoint₃-function-imprecision =
  CTI.ƛ⊑ƛ²
    (CTI.x⊑x²
      {p = I.⇒⊑⇒ checkpoint₃-variable-imprecision I.★⊑★} Z Z)

checkpoint₃-beta-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    C.ƛ (C.` 0) ⊑ checkpoint₁-target-beta-reveal
    ∶ I.⇒⊑⇒
        (I.⇒⊑⇒ checkpoint₃-alpha-variable-imprecision I.★⊑★)
        (I.⇒⊑⇒ checkpoint₃-alpha-variable-imprecision I.★⊑★)
checkpoint₃-beta-imprecision =
  CTI.⊑reveal-rebase²
    checkpoint₁-beta-higher-reveal⊢
    (source-rebase-now TIR.checkpoint₃-beta-ok
      TIR.checkpoint₃-beta-representation)
    checkpoint₃-function-imprecision
    (I.⇒⊑⇒
      (I.⇒⊑⇒ checkpoint₃-alpha-variable-imprecision I.★⊑★)
      (I.⇒⊑⇒ checkpoint₃-alpha-variable-imprecision I.★⊑★))

checkpoint₃-reveals-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    ((C.ƛ (C.` 0)) C.↑
      ((unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★) Conv.↦↑
        (seal Fin.zero ℕᵗ Conv.↦↑ Conv.id↑ ★)))
    ⊑ checkpoint₁-target-payload
    ∶ higher-ℕ⊑higher-dynamic
checkpoint₃-reveals-imprecision =
  CTI.reveal⊑reveal²
    checkpoint₃-source-higher-reveal⊢
    checkpoint₁-alpha-higher-reveal⊢
    refl refl I.ι⊑★
    checkpoint₃-beta-imprecision
    higher-ℕ⊑higher-dynamic

checkpoint₃-source-argument-id-function :
  renameEnv∼ (Consistency.skip id↪ᵗ) (idᶜ {Δ = 0}) ⊢
    (ℕᵗ ⇒ ★) ∼ (ℕᵗ ⇒ ★)
checkpoint₃-source-argument-id-function = id (‵ `ℕ) ↦ id ★

checkpoint₃-argument-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    (applyTerm (bind ℕᵗ)
      (applyTerm keep
        (applyTerm keep
          (proj₁ (compile {Σ = store-empty} more-argument-⊢)
            C.⟨ symᶜ (id (‵ `ℕ) ↦ id ★) ⟩))))
    ⊑ (applyTerm keep
      (applyTerm (bind (＇ Fin.zero))
        (applyTerm (bind ★)
          (proj₁ (compile {Σ = store-empty} less-argument-⊢)
            C.⟨ symᶜ (id ★ ↦ id ★) ⟩))))
    ∶ ℕ⇒★⊑★⇒★
checkpoint₃-argument-imprecision =
  CTI.cast⊑cast²
    checkpoint₃-source-argument-id-function
    checkpoint₁-target-argument-id-function
    (CTI.ƛ⊑ƛ² {pA = I.ι⊑★} {pB = I.★⊑★}
      (CTI.·⊑·²
        (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
          (CTI.x⊑x² {p = I.★⊑★} Z Z))
        (CTI.cast⊑cast²
          (renameᵐᶜ (Consistency.skip id↪ᵗ) (id (‵ `ℕ) !))
          checkpoint₁-target-argument-id-star
          (CTI.x⊑x² {p = I.ι⊑★} Z Z)
          I.★⊑★)))
    ℕ⇒★⊑★⇒★

checkpoint₃-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
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
        (CTI.·⊑·²
          (CTI.cast⊑cast²
            checkpoint₃-source-id-higher
            checkpoint₁-target-id-higher
            checkpoint₃-reveals-imprecision
            higher-ℕ⊑higher-dynamic)
          checkpoint₃-argument-imprecision)
      (CTI.cast⊑cast²
        (renameᵐᶜ (Consistency.skip id↪ᵗ)
          (symᶜ (id (‵ `ℕ))))
        (id (‵ `ℕ) !)
        (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
        I.ι⊑★))
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₃-ladder : String
checkpoint₃-ladder = impLadderDefault checkpoint₃-imprecision


------------------------------------------------------------------------
-- Checkpoint 4: the paired higher identity cast has distributed
------------------------------------------------------------------------

checkpoint₄-source-domain-id :
  flipᵐ (extᵐ (idᶜ {Δ = 0})) ⊢
    (ℕᵗ ⇒ ★) ∼ (ℕᵗ ⇒ ★)
checkpoint₄-source-domain-id with checkpoint₃-source-id-higher
checkpoint₄-source-domain-id | c ↦ d = c

checkpoint₄-source-result-id :
  extᵐ (idᶜ {Δ = 0}) ⊢ (ℕᵗ ⇒ ★) ∼ (ℕᵗ ⇒ ★)
checkpoint₄-source-result-id with checkpoint₃-source-id-higher
checkpoint₄-source-result-id | c ↦ d = d

checkpoint₄-target-domain-id :
  flipᵐ (applyEnv (bind (＇ Fin.zero))
    (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0}))) ⊢
    dynamic-function ∼ dynamic-function
checkpoint₄-target-domain-id with checkpoint₁-target-id-higher
checkpoint₄-target-domain-id | c ↦ d = c

checkpoint₄-target-result-id :
  applyEnv (bind (＇ Fin.zero))
    (renameEnv∼ wk↪ᵗ (idᶜ {Δ = 0})) ⊢
    dynamic-function ∼ dynamic-function
checkpoint₄-target-result-id with checkpoint₁-target-id-higher
checkpoint₄-target-result-id | c ↦ d = d

checkpoint₄-argument-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    ((applyTerm (bind ℕᵗ)
      (applyTerm keep
        (applyTerm keep
          (proj₁ (compile {Σ = store-empty} more-argument-⊢)
            C.⟨ symᶜ (id (‵ `ℕ) ↦ id ★) ⟩)))) C.⟨
      checkpoint₄-source-domain-id ⟩)
    ⊑ ((applyTerm keep
      (applyTerm (bind (＇ Fin.zero))
        (applyTerm (bind ★)
          (proj₁ (compile {Σ = store-empty} less-argument-⊢)
            C.⟨ symᶜ (id ★ ↦ id ★) ⟩)))) C.⟨
      checkpoint₄-target-domain-id ⟩)
    ∶ ℕ⇒★⊑★⇒★
checkpoint₄-argument-imprecision =
  CTI.cast⊑cast²
    checkpoint₄-source-domain-id
    checkpoint₄-target-domain-id
    checkpoint₃-argument-imprecision
    ℕ⇒★⊑★⇒★

checkpoint₄-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    more-checkpoint₄ ⊑ less-checkpoint₄ ∶ I.ι⊑ι
checkpoint₄-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      _ _
      (CTI.·⊑·²
        (CTI.cast⊑cast²
          checkpoint₄-source-result-id
          checkpoint₄-target-result-id
          (CTI.·⊑·²
            checkpoint₃-reveals-imprecision
            checkpoint₄-argument-imprecision)
          ℕ⇒★⊑★⇒★)
        (CTI.cast⊑cast²
          _ _
          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
          I.ι⊑★))
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₄-ladder : String
checkpoint₄-ladder = impLadderDefault checkpoint₄-imprecision


------------------------------------------------------------------------
-- Checkpoint 5: paired alpha conceal and reveal boundaries
------------------------------------------------------------------------

checkpoint₅-source-domain-conceal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↓[ Fin.zero ⦂ ℕᵗ ]
    (Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★)
checkpoint₅-source-domain-conceal⊢ =
  Conv.⊢↓-⇒
    (Conv.⊢↑-unseal TIR.checkpoint₃-source-member)
    (Conv.⊢↓-id-star TIR.checkpoint₃-source-member)

checkpoint₅-alpha-domain-conceal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↓[ Fin.suc Fin.zero ⦂ ★ ]
      (Conv.unseal (Fin.suc Fin.zero) ★ Conv.↦↓ Conv.id↓ ★)
checkpoint₅-alpha-domain-conceal⊢ =
  Conv.⊢↓-⇒
    (Conv.⊢↑-unseal TIR.checkpoint₁-alpha-member)
    (Conv.⊢↓-id-star TIR.checkpoint₁-alpha-member)

checkpoint₅-source-result-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    (Conv.seal Fin.zero ℕᵗ Conv.↦↑ Conv.id↑ ★)
checkpoint₅-source-result-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal TIR.checkpoint₃-source-member)
    (Conv.⊢↑-id-star TIR.checkpoint₃-source-member)

checkpoint₅-alpha-result-reveal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↑[ Fin.suc Fin.zero ⦂ ★ ]
      (Conv.seal (Fin.suc Fin.zero) ★ Conv.↦↑ Conv.id↑ ★)
checkpoint₅-alpha-result-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal TIR.checkpoint₁-alpha-member)
    (Conv.⊢↑-id-star TIR.checkpoint₁-alpha-member)

checkpoint₅-concealed-argument-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    ((applyTerm (bind ℕᵗ)
      (applyTerm keep
        (applyTerm keep
          (proj₁ (compile {Σ = store-empty} more-argument-⊢)
            C.⟨ symᶜ (id (‵ `ℕ) ↦ id ★) ⟩)))) C.⟨
      checkpoint₄-source-domain-id ⟩) C.↓
      (Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★)
    ⊑ ((applyTerm keep
      (applyTerm (bind (＇ Fin.zero))
        (applyTerm (bind ★)
          (proj₁ (compile {Σ = store-empty} less-argument-⊢)
            C.⟨ symᶜ (id ★ ↦ id ★) ⟩)))) C.⟨
      checkpoint₄-target-domain-id ⟩) C.↓
      (Conv.unseal (Fin.suc Fin.zero) ★ Conv.↦↓ Conv.id↓ ★)
    ∶ I.⇒⊑⇒ checkpoint₃-alpha-variable-imprecision I.★⊑★
checkpoint₅-concealed-argument-imprecision =
  CTI.conceal⊑conceal²
    checkpoint₅-source-domain-conceal⊢
    checkpoint₅-alpha-domain-conceal⊢
    refl refl I.ι⊑★
    checkpoint₄-argument-imprecision
    (I.⇒⊑⇒ checkpoint₃-alpha-variable-imprecision I.★⊑★)

checkpoint₅-application-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    (C.ƛ (C.` 0)) C.·
      (((applyTerm (bind ℕᵗ)
        (applyTerm keep
          (applyTerm keep
            (proj₁ (compile {Σ = store-empty} more-argument-⊢)
              C.⟨ symᶜ (id (‵ `ℕ) ↦ id ★) ⟩)))) C.⟨
        checkpoint₄-source-domain-id ⟩) C.↓
        (Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★))
    ⊑ checkpoint₁-target-beta-reveal C.·
      (((applyTerm keep
        (applyTerm (bind (＇ Fin.zero))
          (applyTerm (bind ★)
            (proj₁ (compile {Σ = store-empty} less-argument-⊢)
              C.⟨ symᶜ (id ★ ↦ id ★) ⟩)))) C.⟨
        checkpoint₄-target-domain-id ⟩) C.↓
        (Conv.unseal (Fin.suc Fin.zero) ★ Conv.↦↓ Conv.id↓ ★))
    ∶ I.⇒⊑⇒ checkpoint₃-alpha-variable-imprecision I.★⊑★
checkpoint₅-application-imprecision =
  CTI.·⊑·²
    checkpoint₃-beta-imprecision
    checkpoint₅-concealed-argument-imprecision

checkpoint₅-result-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    (((C.ƛ (C.` 0)) C.·
      (((applyTerm (bind ℕᵗ)
        (applyTerm keep
          (applyTerm keep
            (proj₁ (compile {Σ = store-empty} more-argument-⊢)
              C.⟨ symᶜ (id (‵ `ℕ) ↦ id ★) ⟩)))) C.⟨
        checkpoint₄-source-domain-id ⟩) C.↓
        (Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★))) C.↑
      (Conv.seal Fin.zero ℕᵗ Conv.↦↑ Conv.id↑ ★))
    ⊑ ((checkpoint₁-target-beta-reveal C.·
      (((applyTerm keep
        (applyTerm (bind (＇ Fin.zero))
          (applyTerm (bind ★)
            (proj₁ (compile {Σ = store-empty} less-argument-⊢)
              C.⟨ symᶜ (id ★ ↦ id ★) ⟩)))) C.⟨
        checkpoint₄-target-domain-id ⟩) C.↓
        (Conv.unseal (Fin.suc Fin.zero) ★ Conv.↦↓ Conv.id↓ ★))) C.↑
      (Conv.seal (Fin.suc Fin.zero) ★ Conv.↦↑ Conv.id↑ ★))
    ∶ ℕ⇒★⊑★⇒★
checkpoint₅-result-imprecision =
  CTI.reveal⊑reveal²
    checkpoint₅-source-result-reveal⊢
    checkpoint₅-alpha-result-reveal⊢
    refl refl I.ι⊑★
    checkpoint₅-application-imprecision
    ℕ⇒★⊑★⇒★

checkpoint₅-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    more-checkpoint₅ ⊑ less-checkpoint₅ ∶ I.ι⊑ι
checkpoint₅-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      _ _
      (CTI.·⊑·²
        (CTI.cast⊑cast²
          checkpoint₄-source-result-id
          checkpoint₄-target-result-id
          checkpoint₅-result-imprecision
          ℕ⇒★⊑★⇒★)
        (CTI.cast⊑cast²
          _ _
          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
          I.ι⊑★))
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₅-ladder : String
checkpoint₅-ladder = impLadderDefault checkpoint₅-imprecision


------------------------------------------------------------------------
-- Checkpoint 6: target beta conceal and reveal boundaries
------------------------------------------------------------------------

checkpoint₆-beta-domain-conceal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↓[ Fin.zero ⦂ ＇ (Fin.suc Fin.zero) ]
      (Conv.unseal Fin.zero (＇ (Fin.suc Fin.zero)) Conv.↦↓
        Conv.id↓ ★)
checkpoint₆-beta-domain-conceal⊢ =
  Conv.⊢↓-⇒
    (Conv.⊢↑-unseal TIR.checkpoint₁-beta-member)
    (Conv.⊢↓-id-star TIR.checkpoint₁-beta-member)

checkpoint₆-beta-domain-active :
  concealGeneratorPosition checkpoint₆-beta-domain-conceal⊢
    ≢ generator-absent
checkpoint₆-beta-domain-active ()

checkpoint₆-beta-result-reveal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↑[ Fin.zero ⦂ ＇ (Fin.suc Fin.zero) ]
      (Conv.seal Fin.zero (＇ (Fin.suc Fin.zero)) Conv.↦↑
        Conv.id↑ ★)
checkpoint₆-beta-result-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal TIR.checkpoint₁-beta-member)
    (Conv.⊢↑-id-star TIR.checkpoint₁-beta-member)

checkpoint₆-beta-result-active :
  revealGeneratorPosition checkpoint₆-beta-result-reveal⊢
    ≢ generator-absent
checkpoint₆-beta-result-active ()

checkpoint₆-beta-concealed-argument-imprecision :
  TIR.checkpoint₃-beta-current CTI.⊢²
    ((applyTerm (bind ℕᵗ)
      (applyTerm keep
        (applyTerm keep
          (proj₁ (compile {Σ = store-empty} more-argument-⊢)
            C.⟨ symᶜ (id (‵ `ℕ) ↦ id ★) ⟩)))) C.⟨
      checkpoint₄-source-domain-id ⟩) C.↓
      (Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★)
    ⊑ (((applyTerm keep
      (applyTerm (bind (＇ Fin.zero))
        (applyTerm (bind ★)
          (proj₁ (compile {Σ = store-empty} less-argument-⊢)
            C.⟨ symᶜ (id ★ ↦ id ★) ⟩)))) C.⟨
      checkpoint₄-target-domain-id ⟩) C.↓
      (Conv.unseal (Fin.suc Fin.zero) ★ Conv.↦↓ Conv.id↓ ★)) C.↓
      (Conv.unseal Fin.zero (＇ (Fin.suc Fin.zero)) Conv.↦↓
        Conv.id↓ ★)
    ∶ I.⇒⊑⇒ checkpoint₃-variable-imprecision I.★⊑★
checkpoint₆-beta-concealed-argument-imprecision =
  CTI.⊑conceal-rebase²
    checkpoint₆-beta-domain-conceal⊢
    (source-rebase-now TIR.checkpoint₃-beta-ok
      TIR.checkpoint₃-beta-representation)
    checkpoint₅-concealed-argument-imprecision
    (I.⇒⊑⇒ checkpoint₃-variable-imprecision I.★⊑★)

checkpoint₆-source-argument : Term 1
checkpoint₆-source-argument =
  ((applyTerm (bind ℕᵗ)
    (applyTerm keep
      (applyTerm keep
        (proj₁ (compile {Σ = store-empty} more-argument-⊢)
          C.⟨ symᶜ (id (‵ `ℕ) ↦ id ★) ⟩)))) C.⟨
    checkpoint₄-source-domain-id ⟩) C.↓
    (Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★)

checkpoint₆-target-argument : Term 2
checkpoint₆-target-argument =
  (((applyTerm keep
    (applyTerm (bind (＇ Fin.zero))
      (applyTerm (bind ★)
        (proj₁ (compile {Σ = store-empty} less-argument-⊢)
          C.⟨ symᶜ (id ★ ↦ id ★) ⟩)))) C.⟨
    checkpoint₄-target-domain-id ⟩) C.↓
    (Conv.unseal (Fin.suc Fin.zero) ★ Conv.↦↓ Conv.id↓ ★)) C.↓
    (Conv.unseal Fin.zero (＇ (Fin.suc Fin.zero)) Conv.↦↓
      Conv.id↓ ★)

checkpoint₆-beta-result-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    checkpoint₆-source-argument
    ⊑ checkpoint₆-target-argument C.↑
        (Conv.seal Fin.zero (＇ (Fin.suc Fin.zero)) Conv.↦↑
          Conv.id↑ ★)
    ∶ I.⇒⊑⇒ checkpoint₃-alpha-variable-imprecision I.★⊑★
checkpoint₆-beta-result-imprecision =
  CTI.⊑reveal-rebase²
    checkpoint₆-beta-result-reveal⊢
    (source-rebase-now TIR.checkpoint₃-beta-ok
      TIR.checkpoint₃-beta-representation)
    checkpoint₆-beta-concealed-argument-imprecision
    (I.⇒⊑⇒ checkpoint₃-alpha-variable-imprecision I.★⊑★)

checkpoint₆-result-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    (checkpoint₆-source-argument C.↑
      (Conv.seal Fin.zero ℕᵗ Conv.↦↑ Conv.id↑ ★))
    ⊑ ((checkpoint₆-target-argument C.↑
      (Conv.seal Fin.zero (＇ (Fin.suc Fin.zero)) Conv.↦↑
        Conv.id↑ ★)) C.↑
      (Conv.seal (Fin.suc Fin.zero) ★ Conv.↦↑ Conv.id↑ ★))
    ∶ ℕ⇒★⊑★⇒★
checkpoint₆-result-imprecision =
  CTI.reveal⊑reveal²
    checkpoint₅-source-result-reveal⊢
    checkpoint₅-alpha-result-reveal⊢
    refl refl I.ι⊑★
    checkpoint₆-beta-result-imprecision
    ℕ⇒★⊑★⇒★

checkpoint₆-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    more-checkpoint₆ ⊑ less-checkpoint₆ ∶ I.ι⊑ι
checkpoint₆-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      _ _
      (CTI.·⊑·²
        (CTI.cast⊑cast²
          checkpoint₄-source-result-id
          checkpoint₄-target-result-id
          checkpoint₆-result-imprecision
          ℕ⇒★⊑★⇒★)
        (CTI.cast⊑cast²
          _ _
          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
          I.ι⊑★))
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₆-ladder : String
checkpoint₆-ladder = impLadderDefault checkpoint₆-imprecision


------------------------------------------------------------------------
-- Checkpoint 7: the source data identity cast has erased
------------------------------------------------------------------------

checkpoint₇-data-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    C.$ (κℕ 42)
    ⊑ C.$ (κℕ 42) C.⟨ TIR.checkpoint₃-target-nat-to-star ⟩
    ∶ I.ι⊑★
checkpoint₇-data-imprecision =
  CTI.⊑cast²
    TIR.checkpoint₃-target-nat-to-star
    (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
    I.ι⊑★

checkpoint₇-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    more-checkpoint₇ ⊑ less-checkpoint₇ ∶ I.ι⊑ι
checkpoint₇-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      _ _
      (CTI.·⊑·²
        (CTI.cast⊑cast²
          checkpoint₄-source-result-id
          checkpoint₄-target-result-id
          checkpoint₆-result-imprecision
          ℕ⇒★⊑★⇒★)
        checkpoint₇-data-imprecision)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₇-ladder : String
checkpoint₇-ladder = impLadderDefault checkpoint₇-imprecision


------------------------------------------------------------------------
-- Checkpoints 8–9: the result identity cast has distributed
------------------------------------------------------------------------

checkpoint₈-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    more-checkpoint₈ ⊑ less-checkpoint₈ ∶ I.ι⊑ι
checkpoint₈-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      _ _
      (CTI.cast⊑cast²
        _ _
        (CTI.·⊑·²
          checkpoint₆-result-imprecision
          (CTI.⊑cast²
            _
            (CTI.cast⊑cast²
              _ TIR.checkpoint₃-target-nat-to-star
              (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
              I.ι⊑★)
            I.ι⊑★))
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₈-ladder : String
checkpoint₈-ladder = impLadderDefault checkpoint₈-imprecision

checkpoint₉-imprecision :
  TIR.checkpoint₃-world CTI.⊢²
    more-checkpoint₉ ⊑ less-checkpoint₉ ∶ I.ι⊑ι
checkpoint₉-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      _ _
      (CTI.cast⊑cast²
        _ _
        (CTI.·⊑·²
          checkpoint₆-result-imprecision
          (CTI.⊑cast²
            TIR.checkpoint₃-target-nat-to-star
            (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
            I.ι⊑★))
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₉-ladder : String
checkpoint₉-ladder = impLadderDefault checkpoint₉-imprecision


------------------------------------------------------------------------
-- Checkpoint 10: both active seals are exposed
------------------------------------------------------------------------

checkpoint₁₀-core-imprecision :
  TIR.checkpoint₃-beta-current CTI.⊢²
    checkpoint₆-source-argument C.·
      (C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ)
    ⊑ checkpoint₆-target-argument C.·
      (((C.$ (κℕ 42) C.⟨ TIR.checkpoint₃-target-nat-to-star ⟩)
        C.↓ Conv.seal (Fin.suc Fin.zero) ★) C.↓
        Conv.seal Fin.zero (＇ (Fin.suc Fin.zero)))
    ∶ I.★⊑★
checkpoint₁₀-core-imprecision =
  CTI.·⊑·²
    checkpoint₆-beta-concealed-argument-imprecision
    TIR.checkpoint₈-beta-conceal-imprecision

checkpoint₁₀-identity-reveals-imprecision :
  TIR.checkpoint₃-beta-current CTI.⊢²
    (checkpoint₆-source-argument C.·
      (C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ)) C.↑
      Conv.id↑ ★
    ⊑ ((checkpoint₆-target-argument C.·
      (((C.$ (κℕ 42) C.⟨ TIR.checkpoint₃-target-nat-to-star ⟩)
        C.↓ Conv.seal (Fin.suc Fin.zero) ★) C.↓
        Conv.seal Fin.zero (＇ (Fin.suc Fin.zero)))) C.↑
        Conv.id↑ ★) C.↑ Conv.id↑ ★
    ∶ I.★⊑★
checkpoint₁₀-identity-reveals-imprecision =
  CTI.⊑reveal-identity
    TIR.checkpoint₇-alpha-identity-reveal⊢
    TIR.checkpoint₈-alpha-identity-absent
    (CTI.⊑reveal-identity
      TIR.checkpoint₈-beta-identity-reveal⊢
      TIR.checkpoint₈-beta-identity-absent
      (CTI.reveal⊑-identity
        TIR.checkpoint₇-source-identity-reveal⊢
        TIR.checkpoint₈-source-identity-absent
        checkpoint₁₀-core-imprecision
        I.★⊑★)
      I.★⊑★)
    I.★⊑★

checkpoint₁₀-imprecision :
  TIR.checkpoint₃-beta-current CTI.⊢²
    more-checkpoint₁₀ ⊑ less-checkpoint₁₀ ∶ I.ι⊑ι
checkpoint₁₀-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      _ _
      (CTI.cast⊑cast²
        _ _
        checkpoint₁₀-identity-reveals-imprecision
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₀-ladder : String
checkpoint₁₀-ladder = impLadderDefault checkpoint₁₀-imprecision


------------------------------------------------------------------------
-- Checkpoints 11–12: active cancellations leave identity boundaries
------------------------------------------------------------------------

checkpoint₁₁-source-unoccupied : ∀ Xᴿ
  → toRenameᵗ (ηᴿᶜ TIR.checkpoint₃-allocation-world) Xᴿ
    ≢ toRenameᵗ (ηᴸᶜ TIR.checkpoint₃-allocation-world) Fin.zero
checkpoint₁₁-source-unoccupied Fin.zero ()
checkpoint₁₁-source-unoccupied (Fin.suc Fin.zero) ()

checkpoint₁₁-source-seal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↓[ Fin.zero ⦂ ℕᵗ ]
    Conv.seal Fin.zero ℕᵗ
checkpoint₁₁-source-seal⊢ =
  Conv.⊢↓-seal TIR.checkpoint₃-source-member

checkpoint₁₁-source-seal-active :
  concealGeneratorPosition checkpoint₁₁-source-seal⊢
    ≢ generator-absent
checkpoint₁₁-source-seal-active ()

checkpoint₁₁-source-unseal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    Conv.unseal Fin.zero ℕᵗ
checkpoint₁₁-source-unseal⊢ =
  Conv.⊢↑-unseal TIR.checkpoint₃-source-member

checkpoint₁₁-source-unseal-active :
  revealGeneratorPosition checkpoint₁₁-source-unseal⊢
    ≢ generator-absent
checkpoint₁₁-source-unseal-active ()

checkpoint₁₁-source-identity-conceal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↓[ Fin.zero ⦂ ℕᵗ ]
    Conv.id↓ ★
checkpoint₁₁-source-identity-conceal⊢ =
  Conv.⊢↓-id-star TIR.checkpoint₃-source-member

checkpoint₁₁-source-identity-conceal-absent :
  concealGeneratorPosition checkpoint₁₁-source-identity-conceal⊢
    ≡ generator-absent
checkpoint₁₁-source-identity-conceal-absent = refl

checkpoint₁₁-beta-identity-conceal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↓[ Fin.zero ⦂ ＇ (Fin.suc Fin.zero) ] Conv.id↓ ★
checkpoint₁₁-beta-identity-conceal⊢ =
  Conv.⊢↓-id-star TIR.checkpoint₁-beta-member

checkpoint₁₁-beta-identity-conceal-absent :
  concealGeneratorPosition checkpoint₁₁-beta-identity-conceal⊢
    ≡ generator-absent
checkpoint₁₁-beta-identity-conceal-absent = refl

checkpoint₁₁-alpha-identity-conceal⊢ :
  store-bind (store-bind store-empty ★) (＇ Fin.zero)
    Conv.⊢↓[ Fin.suc Fin.zero ⦂ ★ ] Conv.id↓ ★
checkpoint₁₁-alpha-identity-conceal⊢ =
  Conv.⊢↓-id-star TIR.checkpoint₁-alpha-member

checkpoint₁₁-alpha-identity-conceal-absent :
  concealGeneratorPosition checkpoint₁₁-alpha-identity-conceal⊢
    ≡ generator-absent
checkpoint₁₁-alpha-identity-conceal-absent = refl

checkpoint₁₁-tagged-data-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    C.$ (κℕ 42)
    ⊑ C.$ (κℕ 42) C.⟨ TIR.checkpoint₃-target-nat-to-star ⟩
    ∶ I.ι⊑★
checkpoint₁₁-tagged-data-imprecision =
  CTI.⊑cast²
    TIR.checkpoint₃-target-nat-to-star
    (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
    I.ι⊑★

checkpoint₁₁-sealed-data-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ
    ⊑ C.$ (κℕ 42) C.⟨ TIR.checkpoint₃-target-nat-to-star ⟩
    ∶ I.X⊑★ refl
checkpoint₁₁-sealed-data-imprecision =
  CTI.conceal⊑-only²
    checkpoint₁₁-source-seal⊢
    checkpoint₁₁-source-seal-active
    refl checkpoint₁₁-source-unoccupied I.ι⊑★
    checkpoint₁₁-tagged-data-imprecision
    (I.X⊑★ refl)

checkpoint₁₁-data-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    (C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ) C.↑
      Conv.unseal Fin.zero ℕᵗ
    ⊑ C.$ (κℕ 42) C.⟨ TIR.checkpoint₃-target-nat-to-star ⟩
    ∶ I.ι⊑★
checkpoint₁₁-data-imprecision =
  CTI.reveal⊑-only²
    checkpoint₁₁-source-unseal⊢
    checkpoint₁₁-source-unseal-active
    refl checkpoint₁₁-source-unoccupied I.ι⊑★
    checkpoint₁₁-sealed-data-imprecision
    I.ι⊑★

checkpoint₁₁-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₁₁ ⊑ less-checkpoint₁₁ ∶ I.ι⊑ι
checkpoint₁₁-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      _ _
      (CTI.cast⊑cast²
        _ _
        (CTI.⊑reveal-identity
          TIR.checkpoint₇-alpha-identity-reveal⊢
          TIR.checkpoint₈-alpha-identity-absent
          (CTI.⊑reveal-identity
            TIR.checkpoint₈-beta-identity-reveal⊢
            TIR.checkpoint₈-beta-identity-absent
            (CTI.reveal⊑-identity
              TIR.checkpoint₇-source-identity-reveal⊢
              TIR.checkpoint₈-source-identity-absent
              (CTI.⊑conceal-identity
                checkpoint₁₁-alpha-identity-conceal⊢
                checkpoint₁₁-alpha-identity-conceal-absent
                (CTI.⊑conceal-identity
                  checkpoint₁₁-beta-identity-conceal⊢
                  checkpoint₁₁-beta-identity-conceal-absent
                  (CTI.conceal⊑-identity
                    checkpoint₁₁-source-identity-conceal⊢
                    checkpoint₁₁-source-identity-conceal-absent
                    (CTI.·⊑·²
                      (CTI.cast⊑cast² _ _
                        (CTI.cast⊑cast² _ _
                          (CTI.ƛ⊑ƛ²
                            {pA = I.ι⊑★} {pB = I.★⊑★}
                            (CTI.·⊑·²
                              (CTI.ƛ⊑ƛ²
                                {pA = I.★⊑★} {pB = I.★⊑★}
                                (CTI.x⊑x² {p = I.★⊑★} Z Z))
                              (CTI.cast⊑cast² _ _
                                (CTI.x⊑x² {p = I.ι⊑★} Z Z)
                                I.★⊑★)))
                          ℕ⇒★⊑★⇒★)
                        ℕ⇒★⊑★⇒★)
                      checkpoint₁₁-data-imprecision)
                    I.★⊑★)
                  I.★⊑★)
                I.★⊑★)
              I.★⊑★)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₁-ladder : String
checkpoint₁₁-ladder = impLadderDefault checkpoint₁₁-imprecision

checkpoint₁₂-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₁₂ ⊑ less-checkpoint₁₂ ∶ I.ι⊑ι
checkpoint₁₂-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast²
      _ _
      (CTI.cast⊑cast²
        _ _
        (CTI.⊑reveal-identity
          TIR.checkpoint₇-alpha-identity-reveal⊢
          TIR.checkpoint₈-alpha-identity-absent
          (CTI.⊑reveal-identity
            TIR.checkpoint₈-beta-identity-reveal⊢
            TIR.checkpoint₈-beta-identity-absent
            (CTI.reveal⊑-identity
              TIR.checkpoint₇-source-identity-reveal⊢
              TIR.checkpoint₈-source-identity-absent
              (CTI.⊑conceal-identity
                checkpoint₁₁-alpha-identity-conceal⊢
                checkpoint₁₁-alpha-identity-conceal-absent
                (CTI.⊑conceal-identity
                  checkpoint₁₁-beta-identity-conceal⊢
                  checkpoint₁₁-beta-identity-conceal-absent
                  (CTI.conceal⊑-identity
                    checkpoint₁₁-source-identity-conceal⊢
                    checkpoint₁₁-source-identity-conceal-absent
                    (CTI.·⊑·²
                      (CTI.cast⊑cast² _ _
                        (CTI.cast⊑cast² _ _
                          (CTI.ƛ⊑ƛ²
                            {pA = I.ι⊑★} {pB = I.★⊑★}
                            (CTI.·⊑·²
                              (CTI.ƛ⊑ƛ²
                                {pA = I.★⊑★} {pB = I.★⊑★}
                                (CTI.x⊑x² {p = I.★⊑★} Z Z))
                              (CTI.cast⊑cast² _ _
                                (CTI.x⊑x² {p = I.ι⊑★} Z Z)
                                I.★⊑★)))
                          ℕ⇒★⊑★⇒★)
                        ℕ⇒★⊑★⇒★)
                      checkpoint₁₁-tagged-data-imprecision)
                    I.★⊑★)
                  I.★⊑★)
                I.★⊑★)
              I.★⊑★)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₂-ladder : String
checkpoint₁₂-ladder = impLadderDefault checkpoint₁₂-imprecision


------------------------------------------------------------------------
-- Checkpoint 13: the identity conceal has distributed
------------------------------------------------------------------------

checkpoint₁₃-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₁₃ ⊑ less-checkpoint₁₃ ∶ I.ι⊑ι
checkpoint₁₃-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast² _ _
      (CTI.cast⊑cast² _ _
        (CTI.⊑reveal-identity
          TIR.checkpoint₇-alpha-identity-reveal⊢
          TIR.checkpoint₈-alpha-identity-absent
          (CTI.⊑reveal-identity
            TIR.checkpoint₈-beta-identity-reveal⊢
            TIR.checkpoint₈-beta-identity-absent
            (CTI.reveal⊑-identity
              TIR.checkpoint₇-source-identity-reveal⊢
              TIR.checkpoint₈-source-identity-absent
              (CTI.⊑conceal-identity
                checkpoint₁₁-alpha-identity-conceal⊢
                checkpoint₁₁-alpha-identity-conceal-absent
                (CTI.⊑conceal-identity
                  checkpoint₁₁-beta-identity-conceal⊢
                  checkpoint₁₁-beta-identity-conceal-absent
                  (CTI.conceal⊑-identity
                    checkpoint₁₁-source-identity-conceal⊢
                    checkpoint₁₁-source-identity-conceal-absent
                    (CTI.cast⊑cast² _ _
                      (CTI.·⊑·²
                          (CTI.cast⊑cast² _ _
                            (CTI.ƛ⊑ƛ²
                              {pA = I.ι⊑★} {pB = I.★⊑★}
                              (CTI.·⊑·²
                                (CTI.ƛ⊑ƛ²
                                  {pA = I.★⊑★} {pB = I.★⊑★}
                                  (CTI.x⊑x² {p = I.★⊑★} Z Z))
                                (CTI.cast⊑cast² _ _
                                  (CTI.x⊑x² {p = I.ι⊑★} Z Z)
                                  I.★⊑★)))
                            ℕ⇒★⊑★⇒★)
                          (CTI.⊑cast² _
                            (CTI.cast⊑cast² _ _
                              (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
                              I.ι⊑★)
                            I.ι⊑★))
                      I.★⊑★)
                    I.★⊑★)
                  I.★⊑★)
                I.★⊑★)
              I.★⊑★)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₃-ladder : String
checkpoint₁₃-ladder = impLadderDefault checkpoint₁₃-imprecision

checkpoint₁₄-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₁₄ ⊑ less-checkpoint₁₄ ∶ I.ι⊑ι
checkpoint₁₄-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast² _ _
      (CTI.cast⊑cast² _ _
        (CTI.⊑reveal-identity
          TIR.checkpoint₇-alpha-identity-reveal⊢
          TIR.checkpoint₈-alpha-identity-absent
          (CTI.⊑reveal-identity
            TIR.checkpoint₈-beta-identity-reveal⊢
            TIR.checkpoint₈-beta-identity-absent
            (CTI.reveal⊑-identity
              TIR.checkpoint₇-source-identity-reveal⊢
              TIR.checkpoint₈-source-identity-absent
              (CTI.⊑conceal-identity
                checkpoint₁₁-alpha-identity-conceal⊢
                checkpoint₁₁-alpha-identity-conceal-absent
                (CTI.⊑conceal-identity
                  checkpoint₁₁-beta-identity-conceal⊢
                  checkpoint₁₁-beta-identity-conceal-absent
                  (CTI.conceal⊑-identity
                    checkpoint₁₁-source-identity-conceal⊢
                    checkpoint₁₁-source-identity-conceal-absent
                    (CTI.cast⊑cast² _ _
                      (CTI.·⊑·²
                        (CTI.cast⊑cast² _ _
                          (CTI.ƛ⊑ƛ²
                            {pA = I.ι⊑★} {pB = I.★⊑★}
                            (CTI.·⊑·²
                              (CTI.ƛ⊑ƛ²
                                {pA = I.★⊑★} {pB = I.★⊑★}
                                (CTI.x⊑x² {p = I.★⊑★} Z Z))
                              (CTI.cast⊑cast² _ _
                                (CTI.x⊑x² {p = I.ι⊑★} Z Z)
                                I.★⊑★)))
                          ℕ⇒★⊑★⇒★)
                        (CTI.⊑cast² _
                          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
                          I.ι⊑★))
                      I.★⊑★)
                    I.★⊑★)
                  I.★⊑★)
                I.★⊑★)
              I.★⊑★)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₄-ladder : String
checkpoint₁₄-ladder = impLadderDefault checkpoint₁₄-imprecision

checkpoint₁₅-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₁₅ ⊑ less-checkpoint₁₅ ∶ I.ι⊑ι
checkpoint₁₅-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast² _ _
      (CTI.cast⊑cast² _ _
        (CTI.⊑reveal-identity
          TIR.checkpoint₇-alpha-identity-reveal⊢
          TIR.checkpoint₈-alpha-identity-absent
          (CTI.⊑reveal-identity
            TIR.checkpoint₈-beta-identity-reveal⊢
            TIR.checkpoint₈-beta-identity-absent
            (CTI.reveal⊑-identity
              TIR.checkpoint₇-source-identity-reveal⊢
              TIR.checkpoint₈-source-identity-absent
              (CTI.⊑conceal-identity
                checkpoint₁₁-alpha-identity-conceal⊢
                checkpoint₁₁-alpha-identity-conceal-absent
                (CTI.⊑conceal-identity
                  checkpoint₁₁-beta-identity-conceal⊢
                  checkpoint₁₁-beta-identity-conceal-absent
                  (CTI.conceal⊑-identity
                    checkpoint₁₁-source-identity-conceal⊢
                    checkpoint₁₁-source-identity-conceal-absent
                    (CTI.cast⊑cast² _ _
                      (CTI.cast⊑cast² _ _
                        (CTI.·⊑·²
                          (CTI.ƛ⊑ƛ²
                            {pA = I.ι⊑★} {pB = I.★⊑★}
                            (CTI.·⊑·²
                              (CTI.ƛ⊑ƛ²
                                {pA = I.★⊑★} {pB = I.★⊑★}
                                (CTI.x⊑x² {p = I.★⊑★} Z Z))
                              (CTI.cast⊑cast² _ _
                                (CTI.x⊑x² {p = I.ι⊑★} Z Z)
                                I.★⊑★)))
                          (CTI.⊑cast² _
                            (CTI.cast⊑cast² _ _
                              (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
                              I.ι⊑★)
                            I.ι⊑★))
                        I.★⊑★)
                      I.★⊑★)
                    I.★⊑★)
                  I.★⊑★)
                I.★⊑★)
              I.★⊑★)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₅-ladder : String
checkpoint₁₅-ladder = impLadderDefault checkpoint₁₅-imprecision

checkpoint₁₆-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₁₆ ⊑ less-checkpoint₁₆ ∶ I.ι⊑ι
checkpoint₁₆-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast² _ _
      (CTI.cast⊑cast² _ _
        (CTI.⊑reveal-identity
          TIR.checkpoint₇-alpha-identity-reveal⊢
          TIR.checkpoint₈-alpha-identity-absent
          (CTI.⊑reveal-identity
            TIR.checkpoint₈-beta-identity-reveal⊢
            TIR.checkpoint₈-beta-identity-absent
            (CTI.reveal⊑-identity
              TIR.checkpoint₇-source-identity-reveal⊢
              TIR.checkpoint₈-source-identity-absent
              (CTI.⊑conceal-identity
                checkpoint₁₁-alpha-identity-conceal⊢
                checkpoint₁₁-alpha-identity-conceal-absent
                (CTI.⊑conceal-identity
                  checkpoint₁₁-beta-identity-conceal⊢
                  checkpoint₁₁-beta-identity-conceal-absent
                  (CTI.conceal⊑-identity
                    checkpoint₁₁-source-identity-conceal⊢
                    checkpoint₁₁-source-identity-conceal-absent
                    (CTI.cast⊑cast² _ _
                      (CTI.cast⊑cast² _ _
                        (CTI.·⊑·²
                          (CTI.ƛ⊑ƛ²
                            {pA = I.ι⊑★} {pB = I.★⊑★}
                            (CTI.·⊑·²
                              (CTI.ƛ⊑ƛ²
                                {pA = I.★⊑★} {pB = I.★⊑★}
                                (CTI.x⊑x² {p = I.★⊑★} Z Z))
                              (CTI.cast⊑cast² _ _
                                (CTI.x⊑x² {p = I.ι⊑★} Z Z)
                                I.★⊑★)))
                          (CTI.⊑cast² _
                            (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
                            I.ι⊑★))
                        I.★⊑★)
                      I.★⊑★)
                    I.★⊑★)
                  I.★⊑★)
                I.★⊑★)
              I.★⊑★)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₆-ladder : String
checkpoint₁₆-ladder = impLadderDefault checkpoint₁₆-imprecision

checkpoint₁₇-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₁₇ ⊑ less-checkpoint₁₇ ∶ I.ι⊑ι
checkpoint₁₇-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast² _ _
      (CTI.cast⊑cast² _ _
        (CTI.⊑reveal-identity
          TIR.checkpoint₇-alpha-identity-reveal⊢
          TIR.checkpoint₈-alpha-identity-absent
          (CTI.⊑reveal-identity
            TIR.checkpoint₈-beta-identity-reveal⊢
            TIR.checkpoint₈-beta-identity-absent
            (CTI.reveal⊑-identity
              TIR.checkpoint₇-source-identity-reveal⊢
              TIR.checkpoint₈-source-identity-absent
              (CTI.⊑conceal-identity
                checkpoint₁₁-alpha-identity-conceal⊢
                checkpoint₁₁-alpha-identity-conceal-absent
                (CTI.⊑conceal-identity
                  checkpoint₁₁-beta-identity-conceal⊢
                  checkpoint₁₁-beta-identity-conceal-absent
                  (CTI.conceal⊑-identity
                    checkpoint₁₁-source-identity-conceal⊢
                    checkpoint₁₁-source-identity-conceal-absent
                    (CTI.cast⊑cast² _ _
                      (CTI.cast⊑cast² _ _
                        (CTI.·⊑·²
                          (CTI.ƛ⊑ƛ²
                            {pA = I.★⊑★} {pB = I.★⊑★}
                            (CTI.x⊑x² {p = I.★⊑★} Z Z))
                          (CTI.⊑cast² _
                            (CTI.cast⊑cast² _ _
                              (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
                              I.★⊑★)
                            I.★⊑★))
                        I.★⊑★)
                      I.★⊑★)
                    I.★⊑★)
                  I.★⊑★)
                I.★⊑★)
              I.★⊑★)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₇-ladder : String
checkpoint₁₇-ladder = impLadderDefault checkpoint₁₇-imprecision

checkpoint₁₈-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₁₈ ⊑ less-checkpoint₁₈ ∶ I.ι⊑ι
checkpoint₁₈-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast² _ _
      (CTI.cast⊑cast² _ _
        (CTI.⊑reveal-identity
          TIR.checkpoint₇-alpha-identity-reveal⊢
          TIR.checkpoint₈-alpha-identity-absent
          (CTI.⊑reveal-identity
            TIR.checkpoint₈-beta-identity-reveal⊢
            TIR.checkpoint₈-beta-identity-absent
            (CTI.reveal⊑-identity
              TIR.checkpoint₇-source-identity-reveal⊢
              TIR.checkpoint₈-source-identity-absent
              (CTI.⊑conceal-identity
                checkpoint₁₁-alpha-identity-conceal⊢
                checkpoint₁₁-alpha-identity-conceal-absent
                (CTI.⊑conceal-identity
                  checkpoint₁₁-beta-identity-conceal⊢
                  checkpoint₁₁-beta-identity-conceal-absent
                  (CTI.conceal⊑-identity
                    checkpoint₁₁-source-identity-conceal⊢
                    checkpoint₁₁-source-identity-conceal-absent
                    (CTI.cast⊑cast² _ _
                      (CTI.cast⊑cast² _ _
                        (CTI.cast⊑cast² _ _
                          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
                          I.★⊑★)
                        I.★⊑★)
                      I.★⊑★)
                    I.★⊑★)
                  I.★⊑★)
                I.★⊑★)
              I.★⊑★)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₈-ladder : String
checkpoint₁₈-ladder = impLadderDefault checkpoint₁₈-imprecision

checkpoint₁₉-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₁₉ ⊑ less-checkpoint₁₉ ∶ I.ι⊑ι
checkpoint₁₉-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast² _ _
      (CTI.cast⊑cast² _ _
        (CTI.⊑reveal-identity
          TIR.checkpoint₇-alpha-identity-reveal⊢
          TIR.checkpoint₈-alpha-identity-absent
          (CTI.⊑reveal-identity
            TIR.checkpoint₈-beta-identity-reveal⊢
            TIR.checkpoint₈-beta-identity-absent
            (CTI.reveal⊑-identity
              TIR.checkpoint₇-source-identity-reveal⊢
              TIR.checkpoint₈-source-identity-absent
              (CTI.⊑conceal-identity
                checkpoint₁₁-alpha-identity-conceal⊢
                checkpoint₁₁-alpha-identity-conceal-absent
                (CTI.⊑conceal-identity
                  checkpoint₁₁-beta-identity-conceal⊢
                  checkpoint₁₁-beta-identity-conceal-absent
                  (CTI.conceal⊑-identity
                    checkpoint₁₁-source-identity-conceal⊢
                    checkpoint₁₁-source-identity-conceal-absent
                    (CTI.cast⊑cast² _ _
                      (CTI.cast⊑cast² _ _
                        (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
                        I.★⊑★)
                      I.★⊑★)
                    I.★⊑★)
                  I.★⊑★)
                I.★⊑★)
              I.★⊑★)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₁₉-ladder : String
checkpoint₁₉-ladder = impLadderDefault checkpoint₁₉-imprecision

checkpoint₂₀-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₂₀ ⊑ less-checkpoint₂₀ ∶ I.ι⊑ι
checkpoint₂₀-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast² _ _
      (CTI.cast⊑cast² _ _
        (CTI.⊑reveal-identity
          TIR.checkpoint₇-alpha-identity-reveal⊢
          TIR.checkpoint₈-alpha-identity-absent
          (CTI.⊑reveal-identity
            TIR.checkpoint₈-beta-identity-reveal⊢
            TIR.checkpoint₈-beta-identity-absent
            (CTI.reveal⊑-identity
              TIR.checkpoint₇-source-identity-reveal⊢
              TIR.checkpoint₈-source-identity-absent
              (CTI.⊑conceal-identity
                checkpoint₁₁-alpha-identity-conceal⊢
                checkpoint₁₁-alpha-identity-conceal-absent
                (CTI.⊑conceal-identity
                  checkpoint₁₁-beta-identity-conceal⊢
                  checkpoint₁₁-beta-identity-conceal-absent
                  (CTI.conceal⊑-identity
                    checkpoint₁₁-source-identity-conceal⊢
                    checkpoint₁₁-source-identity-conceal-absent
                    (CTI.cast⊑cast² _ _
                      (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
                      I.★⊑★)
                    I.★⊑★)
                  I.★⊑★)
                I.★⊑★)
              I.★⊑★)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₂₀-ladder : String
checkpoint₂₀-ladder = impLadderDefault checkpoint₂₀-imprecision

checkpoint₂₁-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₂₁ ⊑ less-checkpoint₂₁ ∶ I.ι⊑ι
checkpoint₂₁-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast² _ _
      (CTI.cast⊑cast² _ _
        (CTI.⊑reveal-identity
          TIR.checkpoint₇-alpha-identity-reveal⊢
          TIR.checkpoint₈-alpha-identity-absent
          (CTI.⊑reveal-identity
            TIR.checkpoint₈-beta-identity-reveal⊢
            TIR.checkpoint₈-beta-identity-absent
            (CTI.reveal⊑-identity
              TIR.checkpoint₇-source-identity-reveal⊢
              TIR.checkpoint₈-source-identity-absent
              (CTI.⊑conceal-identity
                checkpoint₁₁-alpha-identity-conceal⊢
                checkpoint₁₁-alpha-identity-conceal-absent
                (CTI.cast⊑cast² _ _
                  (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
                  I.★⊑★)
                I.★⊑★)
              I.★⊑★)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₂₁-ladder : String
checkpoint₂₁-ladder = impLadderDefault checkpoint₂₁-imprecision

checkpoint₂₂-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₂₂ ⊑ less-checkpoint₂₂ ∶ I.ι⊑ι
checkpoint₂₂-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast² _ _
      (CTI.cast⊑cast² _ _
        (CTI.⊑reveal-identity
          TIR.checkpoint₇-alpha-identity-reveal⊢
          TIR.checkpoint₈-alpha-identity-absent
          (CTI.cast⊑cast² _ _
            (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₂₂-ladder : String
checkpoint₂₂-ladder = impLadderDefault checkpoint₂₂-imprecision

checkpoint₂₃-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₂₃ ⊑ less-checkpoint₂₃ ∶ I.ι⊑ι
checkpoint₂₃-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.cast⊑cast² _ _
      (CTI.⊑cast² _
        (CTI.cast⊑cast² _ _
          (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))
          I.★⊑★)
        I.★⊑★)
      (I.ι⊑ι {ι = `ℕ}))

checkpoint₂₃-ladder : String
checkpoint₂₃-ladder = impLadderDefault checkpoint₂₃-imprecision

checkpoint₂₄-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₂₄ ⊑ less-checkpoint₂₄ ∶ I.ι⊑ι
checkpoint₂₄-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ²
      (CTI.x⊑x² {p = I.ι⊑ι {ι = `ℕ}} Z Z))
    (CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ}))

checkpoint₂₄-ladder : String
checkpoint₂₄-ladder = impLadderDefault checkpoint₂₄-imprecision

checkpoint₂₅-imprecision :
  TIR.checkpoint₃-allocation-world CTI.⊢²
    more-checkpoint₂₅ ⊑ less-checkpoint₂₅ ∶ I.ι⊑ι
checkpoint₂₅-imprecision =
  CTI.κ⊑κ² (κℕ 42) (I.ι⊑ι {ι = `ℕ})

checkpoint₂₅-ladder : String
checkpoint₂₅-ladder = impLadderDefault checkpoint₂₅-imprecision

checkpoint₀-ladder-pinned :
  checkpoint₀-ladder ≡
    "⟨⟩\n" ++
    "source term                                                    A                                                    ηᴸA                                                  ⊑ costs                                                                                     ηᴿB                                          B                                            target term\n" ++
    "─────────────────────────────────────────────────────────────  ───────────────────────────────────────────────────  ───────────────────────────────────────────────────  ──────────────────────────────────────────────────────────────────────────────────────────  ───────────────────────────────────────────  ───────────────────────────────────────────  ─────────────────────────────────────────────────────────\n" ++
    "□₁ · □₂                                                        ℕ                                                    ℕ                                                    ℕ⊑ℕ                                                                                         ℕ                                            ℕ                                            □₁ · □₂\n" ++
    "├ λ♯0. □                                                       (ℕ ⇒ ℕ)                                              (ℕ ⇒ ℕ)                                              ℕ⊑ℕ, ℕ⊑ℕ                                                                                    (ℕ ⇒ ℕ)                                      (ℕ ⇒ ℕ)                                      ├ λ♯0. □\n" ++
    "│ ♯0                                                           ℕ                                                    ℕ                                                    ℕ⊑ℕ                                                                                         ℕ                                            ℕ                                            │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                                                    ℕ                                                    ℕ                                                    ℕ⊑ℕ                                                                                         ℕ                                            ℕ                                            └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                                                      ★                                                    ★                                                    ★⊑★                                                                                         ★                                            ★                                              □₁ · □₂\n" ++
    "  ├ □₁ · □₂                                                    (ℕ ⇒ ★)                                              (ℕ ⇒ ★)                                              ι⊑★, ★⊑★                                                                                    (★ ⇒ ★)                                      (★ ⇒ ★)                                        ├ □₁ · □₂\n" ++
    "  │ ├ □ [ ℕ ]                                                  ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))                                  ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))                                  ι⊑★, ★⊑★, ι⊑★, ★⊑★                                                                          ((★ ⇒ ★) ⇒ (★ ⇒ ★))                          ((★ ⇒ ★) ⇒ (★ ⇒ ★))                            │ ├ ─\n" ++
    "  │ │ □₁ · □₂                                                  ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                              ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                              ∀⊑(mark X⊑★ at ♭0, ★⊑★, mark X⊑★ at ♭0, ★⊑★)                                                ((★ ⇒ ★) ⇒ (★ ⇒ ★))                          ((★ ⇒ ★) ⇒ (★ ⇒ ★))                            │ │ □₁ · □₂\n" ++
    "  │ │ ├ λ♯0. □                                                 (∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★)) ⇒ ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★)))  (∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★)) ⇒ ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★)))  ∀⊑(mark X⊑★ at ♭0, ★⊑★, mark X⊑★ at ♭0, ★⊑★), ∀⊑(mark X⊑★ at ♭0, ★⊑★, mark X⊑★ at ♭0, ★⊑★)  (((★ ⇒ ★) ⇒ (★ ⇒ ★)) ⇒ ((★ ⇒ ★) ⇒ (★ ⇒ ★)))  (((★ ⇒ ★) ⇒ (★ ⇒ ★)) ⇒ ((★ ⇒ ★) ⇒ (★ ⇒ ★)))    │ │ ├ λ♯0. □\n" ++
    "  │ │ │ ♯0                                                     ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                              ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                              ∀⊑(mark X⊑★ at ♭0, ★⊑★, mark X⊑★ at ♭0, ★⊑★)                                                ((★ ⇒ ★) ⇒ (★ ⇒ ★))                          ((★ ⇒ ★) ⇒ (★ ⇒ ★))                            │ │ │ ♯0\n" ++
    "  │ │ └ □ ⟨ ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))↦∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★)) ⟩  ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                              ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                              ∀⊑(mark X⊑★ at ♭0, ★⊑★, mark X⊑★ at ♭0, ★⊑★)                                                ((★ ⇒ ★) ⇒ (★ ⇒ ★))                          ((★ ⇒ ★) ⇒ (★ ⇒ ★))                            │ │ └ □ ⟨ ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))↦((★ ⇒ ★) ⇒ (★ ⇒ ★)) ⟩\n" ++
    "  │ │   Λ□                                                     ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                              ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                              ∀(♭0 ≈ ♭0, ★⊑★, ♭0 ≈ ♭0, ★⊑★)                                                               ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                      ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                        │ │   Λ□\n" ++
    "  │ │   λ♯0. □                                                 ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                                ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                                ♭0 ≈ ♭0, ★⊑★, ♭0 ≈ ♭0, ★⊑★                                                                  ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                        ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))                          │ │   λ♯0. □\n" ++
    "  │ │   ♯0                                                     (♭0 ⇒ ★)                                             (♭0 ⇒ ★)                                             ♭0 ≈ ♭0, ★⊑★                                                                                (♭0 ⇒ ★)                                     (♭0 ⇒ ★)                                       │ │   ♯0\n" ++
    "  │ └ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩                                    (ℕ ⇒ ★)                                              (ℕ ⇒ ★)                                              ι⊑★, ★⊑★                                                                                    (★ ⇒ ★)                                      (★ ⇒ ★)                                        │ └ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │   λ♯0. □                                                   (ℕ ⇒ ★)                                              (ℕ ⇒ ★)                                              ι⊑★, ★⊑★                                                                                    (★ ⇒ ★)                                      (★ ⇒ ★)                                        │   λ♯0. □\n" ++
    "  │   □₁ · □₂                                                  ★                                                    ★                                                    ★⊑★                                                                                         ★                                            ★                                              │   □₁ · □₂\n" ++
    "  │   ├ λ♯1. □                                                 (★ ⇒ ★)                                              (★ ⇒ ★)                                              ★⊑★, ★⊑★                                                                                    (★ ⇒ ★)                                      (★ ⇒ ★)                                        │   ├ λ♯1. □\n" ++
    "  │   │ ♯1                                                     ★                                                    ★                                                    ★⊑★                                                                                         ★                                            ★                                              │   │ ♯1\n" ++
    "  │   └ □ ⟨ ℕ↦★ ⟩                                              ★                                                    ★                                                    ★⊑★                                                                                         ★                                            ★                                              │   └ □ ⟨ ★↦★ ⟩\n" ++
    "  │     ♯0                                                     ℕ                                                    ℕ                                                    ι⊑★                                                                                         ★                                            ★                                              │     ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩                                                  ℕ                                                    ℕ                                                    ι⊑★                                                                                         ★                                            ★                                              └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                                                         ℕ                                                    ℕ                                                    ℕ⊑ℕ                                                                                         ℕ                                            ℕ                                                42"
checkpoint₀-ladder-pinned = refl
checkpoint₁-ladder-pinned :
  checkpoint₁-ladder ≡
    "⟨X: ─ ⊑[X⊑★] X′↦＇Y′ │ Y: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                                                  A                        ηᴸA                      ⊑ costs                                                   ηᴿB                  B                      target term\n" ++
    "───────────────────────────────────────────────────────────  ───────────────────────  ───────────────────────  ────────────────────────────────────────────────────────  ───────────────────  ─────────────────────  ───────────────────────────────────────────────────\n" ++
    "□₁ · □₂                                                      ℕ                        ℕ                        ℕ⊑ℕ                                                       ℕ                    ℕ                      □₁ · □₂\n" ++
    "├ λ♯0. □                                                     (ℕ ⇒ ℕ)                  (ℕ ⇒ ℕ)                  ℕ⊑ℕ, ℕ⊑ℕ                                                  (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)                ├ λ♯0. □\n" ++
    "│ ♯0                                                         ℕ                        ℕ                        ℕ⊑ℕ                                                       ℕ                    ℕ                      │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                                                  ℕ                        ℕ                        ℕ⊑ℕ                                                       ℕ                    ℕ                      └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                                                    ★                        ★                        ★⊑★                                                       ★                    ★                        □₁ · □₂\n" ++
    "  ├ □₁ · □₂                                                  (ℕ ⇒ ★)                  (ℕ ⇒ ★)                  ι⊑★, ★⊑★                                                  (★ ⇒ ★)              (★ ⇒ ★)                  ├ □₁ · □₂\n" ++
    "  │ ├ □ [ ℕ ]                                                ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))      ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))      ι⊑★, ★⊑★, ι⊑★, ★⊑★                                        ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))      │ ├ ─\n" ++
    "  │ │ □ ⟨ ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))↦∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★)) ⟩  ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))  ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))  ∀⊑(mark X⊑★ at ♭0, ★⊑★, mark X⊑★ at ♭0, ★⊑★)              ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))      │ │ □ ⟨ ((★ ⇒ ★) ⇒ (★ ⇒ ★))↦((★ ⇒ ★) ⇒ (★ ⇒ ★)) ⟩\n" ++
    "  │ │ Λ□                                                     ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))  ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))  ∀⊑(mark X⊑★ at ♭0, ★⊑★, mark X⊑★ at ♭0, ★⊑★)              ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))      │ │ ─\n" ++
    "  │ │ ─                                                      ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))    ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))    mark X⊑★ at ♭0, ★⊑★, mark X⊑★ at ♭0, ★⊑★ + source rebase  ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))      │ │ □ ↑ ⇒-rev\n" ++
    "  │ │ ─                                                      ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))    ((Y ⇒ ★) ⇒ (Y ⇒ ★))      Y ≈ Y, ★⊑★, Y ≈ Y, ★⊑★ + source rebase                    ((Y ⇒ ★) ⇒ (Y ⇒ ★))  ((Y′ ⇒ ★) ⇒ (Y′ ⇒ ★))    │ │ □ ↑ ⇒-rev\n" ++
    "  │ │ λ♯0. □                                                 ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))    ((X ⇒ ★) ⇒ (X ⇒ ★))      X ≈ X, ★⊑★, X ≈ X, ★⊑★                                    ((X ⇒ ★) ⇒ (X ⇒ ★))  ((X′ ⇒ ★) ⇒ (X′ ⇒ ★))    │ │ λ♯0. □\n" ++
    "  │ │ ♯0                                                     (♭0 ⇒ ★)                 (X ⇒ ★)                  X ≈ X, ★⊑★                                                (X ⇒ ★)              (X′ ⇒ ★)                 │ │ ♯0\n" ++
    "  │ └ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩                                  (ℕ ⇒ ★)                  (ℕ ⇒ ★)                  ι⊑★, ★⊑★                                                  (★ ⇒ ★)              (★ ⇒ ★)                  │ └ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │   λ♯0. □                                                 (ℕ ⇒ ★)                  (ℕ ⇒ ★)                  ι⊑★, ★⊑★                                                  (★ ⇒ ★)              (★ ⇒ ★)                  │   λ♯0. □\n" ++
    "  │   □₁ · □₂                                                ★                        ★                        ★⊑★                                                       ★                    ★                        │   □₁ · □₂\n" ++
    "  │   ├ λ♯1. □                                               (★ ⇒ ★)                  (★ ⇒ ★)                  ★⊑★, ★⊑★                                                  (★ ⇒ ★)              (★ ⇒ ★)                  │   ├ λ♯1. □\n" ++
    "  │   │ ♯1                                                   ★                        ★                        ★⊑★                                                       ★                    ★                        │   │ ♯1\n" ++
    "  │   └ □ ⟨ ℕ↦★ ⟩                                            ★                        ★                        ★⊑★                                                       ★                    ★                        │   └ □ ⟨ ★↦★ ⟩\n" ++
    "  │     ♯0                                                   ℕ                        ℕ                        ι⊑★                                                       ★                    ★                        │     ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩                                                ℕ                        ℕ                        ι⊑★                                                       ★                    ★                        └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                                                       ℕ                        ℕ                        ℕ⊑ℕ                                                       ℕ                    ℕ                          42"
checkpoint₁-ladder-pinned = refl
checkpoint₂-ladder-pinned :
  checkpoint₂-ladder ≡
    "⟨X: ─ ⊑[X⊑★] X′↦＇Y′ │ Y: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                                          A                        ηᴸA                      ⊑ costs                                                   ηᴿB                  B                      target term\n" ++
    "───────────────────────────────────────────────────  ───────────────────────  ───────────────────────  ────────────────────────────────────────────────────────  ───────────────────  ─────────────────────  ───────────────────────────────────────────────────\n" ++
    "□₁ · □₂                                              ℕ                        ℕ                        ℕ⊑ℕ                                                       ℕ                    ℕ                      □₁ · □₂\n" ++
    "├ λ♯0. □                                             (ℕ ⇒ ℕ)                  (ℕ ⇒ ℕ)                  ℕ⊑ℕ, ℕ⊑ℕ                                                  (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)                ├ λ♯0. □\n" ++
    "│ ♯0                                                 ℕ                        ℕ                        ℕ⊑ℕ                                                       ℕ                    ℕ                      │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                                          ℕ                        ℕ                        ℕ⊑ℕ                                                       ℕ                    ℕ                      └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                                            ★                        ★                        ★⊑★                                                       ★                    ★                        □₁ · □₂\n" ++
    "  ├ □₁ · □₂                                          (ℕ ⇒ ★)                  (ℕ ⇒ ★)                  ι⊑★, ★⊑★                                                  (★ ⇒ ★)              (★ ⇒ ★)                  ├ □₁ · □₂\n" ++
    "  │ ├ □ ⟨ ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))↦((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★)) ⟩  ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))      ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))      ι⊑★, ★⊑★, ι⊑★, ★⊑★                                        ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))      │ ├ □ ⟨ ((★ ⇒ ★) ⇒ (★ ⇒ ★))↦((★ ⇒ ★) ⇒ (★ ⇒ ★)) ⟩\n" ++
    "  │ │ □ [ ℕ ]                                        ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))      ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))      ι⊑★, ★⊑★, ι⊑★, ★⊑★                                        ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))      │ │ ─\n" ++
    "  │ │ Λ□                                             ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))  ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))  ∀⊑(mark X⊑★ at ♭0, ★⊑★, mark X⊑★ at ♭0, ★⊑★)              ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))      │ │ ─\n" ++
    "  │ │ ─                                              ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))    ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))    mark X⊑★ at ♭0, ★⊑★, mark X⊑★ at ♭0, ★⊑★ + source rebase  ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))      │ │ □ ↑ ⇒-rev\n" ++
    "  │ │ ─                                              ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))    ((Y ⇒ ★) ⇒ (Y ⇒ ★))      Y ≈ Y, ★⊑★, Y ≈ Y, ★⊑★ + source rebase                    ((Y ⇒ ★) ⇒ (Y ⇒ ★))  ((Y′ ⇒ ★) ⇒ (Y′ ⇒ ★))    │ │ □ ↑ ⇒-rev\n" ++
    "  │ │ λ♯0. □                                         ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))    ((X ⇒ ★) ⇒ (X ⇒ ★))      X ≈ X, ★⊑★, X ≈ X, ★⊑★                                    ((X ⇒ ★) ⇒ (X ⇒ ★))  ((X′ ⇒ ★) ⇒ (X′ ⇒ ★))    │ │ λ♯0. □\n" ++
    "  │ │ ♯0                                             (♭0 ⇒ ★)                 (X ⇒ ★)                  X ≈ X, ★⊑★                                                (X ⇒ ★)              (X′ ⇒ ★)                 │ │ ♯0\n" ++
    "  │ └ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩                          (ℕ ⇒ ★)                  (ℕ ⇒ ★)                  ι⊑★, ★⊑★                                                  (★ ⇒ ★)              (★ ⇒ ★)                  │ └ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │   λ♯0. □                                         (ℕ ⇒ ★)                  (ℕ ⇒ ★)                  ι⊑★, ★⊑★                                                  (★ ⇒ ★)              (★ ⇒ ★)                  │   λ♯0. □\n" ++
    "  │   □₁ · □₂                                        ★                        ★                        ★⊑★                                                       ★                    ★                        │   □₁ · □₂\n" ++
    "  │   ├ λ♯1. □                                       (★ ⇒ ★)                  (★ ⇒ ★)                  ★⊑★, ★⊑★                                                  (★ ⇒ ★)              (★ ⇒ ★)                  │   ├ λ♯1. □\n" ++
    "  │   │ ♯1                                           ★                        ★                        ★⊑★                                                       ★                    ★                        │   │ ♯1\n" ++
    "  │   └ □ ⟨ ℕ↦★ ⟩                                    ★                        ★                        ★⊑★                                                       ★                    ★                        │   └ □ ⟨ ★↦★ ⟩\n" ++
    "  │     ♯0                                           ℕ                        ℕ                        ι⊑★                                                       ★                    ★                        │     ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩                                        ℕ                        ℕ                        ι⊑★                                                       ★                    ★                        └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                                               ℕ                        ℕ                        ℕ⊑ℕ                                                       ℕ                    ℕ                          42"
checkpoint₂-ladder-pinned = refl
checkpoint₃-ladder-pinned :
  checkpoint₃-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                                          A                    ηᴸA                  ⊑ costs                                      ηᴿB                  B                      target term\n" ++
    "───────────────────────────────────────────────────  ───────────────────  ───────────────────  ───────────────────────────────────────────  ───────────────────  ─────────────────────  ───────────────────────────────────────────────────\n" ++
    "□₁ · □₂                                              ℕ                    ℕ                    ℕ⊑ℕ                                          ℕ                    ℕ                      □₁ · □₂\n" ++
    "├ λ♯0. □                                             (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)              ℕ⊑ℕ, ℕ⊑ℕ                                     (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)                ├ λ♯0. □\n" ++
    "│ ♯0                                                 ℕ                    ℕ                    ℕ⊑ℕ                                          ℕ                    ℕ                      │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                                          ℕ                    ℕ                    ℕ⊑ℕ                                          ℕ                    ℕ                      └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                                            ★                    ★                    ★⊑★                                          ★                    ★                        □₁ · □₂\n" ++
    "  ├ □₁ · □₂                                          (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                     (★ ⇒ ★)              (★ ⇒ ★)                  ├ □₁ · □₂\n" ++
    "  │ ├ □ ⟨ ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))↦((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★)) ⟩  ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))  ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))  ι⊑★, ★⊑★, ι⊑★, ★⊑★                           ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))      │ ├ □ ⟨ ((★ ⇒ ★) ⇒ (★ ⇒ ★))↦((★ ⇒ ★) ⇒ (★ ⇒ ★)) ⟩\n" ++
    "  │ │ □ ↑ ⇒-rev                                      ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))  ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))  ι⊑★, ★⊑★, ι⊑★, ★⊑★ + matched reveal partner  ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))      │ │ □ ↑ ⇒-rev\n" ++
    "  │ │ ─                                              ((X ⇒ ★) ⇒ (X ⇒ ★))  ((Z ⇒ ★) ⇒ (Z ⇒ ★))  Z ≈ Z, ★⊑★, Z ≈ Z, ★⊑★ + source rebase       ((Z ⇒ ★) ⇒ (Z ⇒ ★))  ((Y′ ⇒ ★) ⇒ (Y′ ⇒ ★))    │ │ □ ↑ ⇒-rev\n" ++
    "  │ │ λ♯0. □                                         ((X ⇒ ★) ⇒ (X ⇒ ★))  ((Y ⇒ ★) ⇒ (Y ⇒ ★))  Y ≈ Y, ★⊑★, Y ≈ Y, ★⊑★                       ((Y ⇒ ★) ⇒ (Y ⇒ ★))  ((X′ ⇒ ★) ⇒ (X′ ⇒ ★))    │ │ λ♯0. □\n" ++
    "  │ │ ♯0                                             (X ⇒ ★)              (Y ⇒ ★)              Y ≈ Y, ★⊑★                                   (Y ⇒ ★)              (X′ ⇒ ★)                 │ │ ♯0\n" ++
    "  │ └ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩                          (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                     (★ ⇒ ★)              (★ ⇒ ★)                  │ └ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │   λ♯0. □                                         (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                     (★ ⇒ ★)              (★ ⇒ ★)                  │   λ♯0. □\n" ++
    "  │   □₁ · □₂                                        ★                    ★                    ★⊑★                                          ★                    ★                        │   □₁ · □₂\n" ++
    "  │   ├ λ♯1. □                                       (★ ⇒ ★)              (★ ⇒ ★)              ★⊑★, ★⊑★                                     (★ ⇒ ★)              (★ ⇒ ★)                  │   ├ λ♯1. □\n" ++
    "  │   │ ♯1                                           ★                    ★                    ★⊑★                                          ★                    ★                        │   │ ♯1\n" ++
    "  │   └ □ ⟨ ℕ↦★ ⟩                                    ★                    ★                    ★⊑★                                          ★                    ★                        │   └ □ ⟨ ★↦★ ⟩\n" ++
    "  │     ♯0                                           ℕ                    ℕ                    ι⊑★                                          ★                    ★                        │     ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩                                        ℕ                    ℕ                    ι⊑★                                          ★                    ★                        └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                                               ℕ                    ℕ                    ℕ⊑ℕ                                          ℕ                    ℕ                          42"
checkpoint₃-ladder-pinned = refl
checkpoint₄-ladder-pinned :
  checkpoint₄-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                  A                    ηᴸA                  ⊑ costs                                      ηᴿB                  B                      target term\n" ++
    "───────────────────────────  ───────────────────  ───────────────────  ───────────────────────────────────────────  ───────────────────  ─────────────────────  ───────────────────────────\n" ++
    "□₁ · □₂                      ℕ                    ℕ                    ℕ⊑ℕ                                          ℕ                    ℕ                      □₁ · □₂\n" ++
    "├ λ♯0. □                     (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)              ℕ⊑ℕ, ℕ⊑ℕ                                     (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)                ├ λ♯0. □\n" ++
    "│ ♯0                         ℕ                    ℕ                    ℕ⊑ℕ                                          ℕ                    ℕ                      │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                  ℕ                    ℕ                    ℕ⊑ℕ                                          ℕ                    ℕ                      └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                    ★                    ★                    ★⊑★                                          ★                    ★                        □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩    (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                     (★ ⇒ ★)              (★ ⇒ ★)                  ├ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □₁ · □₂                  (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                     (★ ⇒ ★)              (★ ⇒ ★)                  │ □₁ · □₂\n" ++
    "  │ ├ □ ↑ ⇒-rev              ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))  ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))  ι⊑★, ★⊑★, ι⊑★, ★⊑★ + matched reveal partner  ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))      │ ├ □ ↑ ⇒-rev\n" ++
    "  │ │ ─                      ((X ⇒ ★) ⇒ (X ⇒ ★))  ((Z ⇒ ★) ⇒ (Z ⇒ ★))  Z ≈ Z, ★⊑★, Z ≈ Z, ★⊑★ + source rebase       ((Z ⇒ ★) ⇒ (Z ⇒ ★))  ((Y′ ⇒ ★) ⇒ (Y′ ⇒ ★))    │ │ □ ↑ ⇒-rev\n" ++
    "  │ │ λ♯0. □                 ((X ⇒ ★) ⇒ (X ⇒ ★))  ((Y ⇒ ★) ⇒ (Y ⇒ ★))  Y ≈ Y, ★⊑★, Y ≈ Y, ★⊑★                       ((Y ⇒ ★) ⇒ (Y ⇒ ★))  ((X′ ⇒ ★) ⇒ (X′ ⇒ ★))    │ │ λ♯0. □\n" ++
    "  │ │ ♯0                     (X ⇒ ★)              (Y ⇒ ★)              Y ≈ Y, ★⊑★                                   (Y ⇒ ★)              (X′ ⇒ ★)                 │ │ ♯0\n" ++
    "  │ └ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                     (★ ⇒ ★)              (★ ⇒ ★)                  │ └ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │   □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                     (★ ⇒ ★)              (★ ⇒ ★)                  │   □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │   λ♯0. □                 (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                     (★ ⇒ ★)              (★ ⇒ ★)                  │   λ♯0. □\n" ++
    "  │   □₁ · □₂                ★                    ★                    ★⊑★                                          ★                    ★                        │   □₁ · □₂\n" ++
    "  │   ├ λ♯1. □               (★ ⇒ ★)              (★ ⇒ ★)              ★⊑★, ★⊑★                                     (★ ⇒ ★)              (★ ⇒ ★)                  │   ├ λ♯1. □\n" ++
    "  │   │ ♯1                   ★                    ★                    ★⊑★                                          ★                    ★                        │   │ ♯1\n" ++
    "  │   └ □ ⟨ ℕ↦★ ⟩            ★                    ★                    ★⊑★                                          ★                    ★                        │   └ □ ⟨ ★↦★ ⟩\n" ++
    "  │     ♯0                   ℕ                    ℕ                    ι⊑★                                          ★                    ★                        │     ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩                ℕ                    ℕ                    ι⊑★                                          ★                    ★                        └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                       ℕ                    ℕ                    ℕ⊑ℕ                                          ℕ                    ℕ                          42"
checkpoint₄-ladder-pinned = refl
checkpoint₅-ladder-pinned :
  checkpoint₅-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                  A                    ηᴸA                  ⊑ costs                                 ηᴿB                  B                      target term\n" ++
    "───────────────────────────  ───────────────────  ───────────────────  ──────────────────────────────────────  ───────────────────  ─────────────────────  ───────────────────────────\n" ++
    "□₁ · □₂                      ℕ                    ℕ                    ℕ⊑ℕ                                     ℕ                    ℕ                      □₁ · □₂\n" ++
    "├ λ♯0. □                     (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)              ℕ⊑ℕ, ℕ⊑ℕ                                (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)                ├ λ♯0. □\n" ++
    "│ ♯0                         ℕ                    ℕ                    ℕ⊑ℕ                                     ℕ                    ℕ                      │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                  ℕ                    ℕ                    ℕ⊑ℕ                                     ℕ                    ℕ                      └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                    ★                    ★                    ★⊑★                                     ★                    ★                        □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩    (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                (★ ⇒ ★)              (★ ⇒ ★)                  ├ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ ↑ ⇒-rev                (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★ + matched reveal partner       (★ ⇒ ★)              (★ ⇒ ★)                  │ □ ↑ ⇒-rev\n" ++
    "  │ □₁ · □₂                  (X ⇒ ★)              (Z ⇒ ★)              Z ≈ Z, ★⊑★                              (Z ⇒ ★)              (Y′ ⇒ ★)                 │ □₁ · □₂\n" ++
    "  │ ├ ─                      ((X ⇒ ★) ⇒ (X ⇒ ★))  ((Z ⇒ ★) ⇒ (Z ⇒ ★))  Z ≈ Z, ★⊑★, Z ≈ Z, ★⊑★ + source rebase  ((Z ⇒ ★) ⇒ (Z ⇒ ★))  ((Y′ ⇒ ★) ⇒ (Y′ ⇒ ★))    │ ├ □ ↑ ⇒-rev\n" ++
    "  │ │ λ♯0. □                 ((X ⇒ ★) ⇒ (X ⇒ ★))  ((Y ⇒ ★) ⇒ (Y ⇒ ★))  Y ≈ Y, ★⊑★, Y ≈ Y, ★⊑★                  ((Y ⇒ ★) ⇒ (Y ⇒ ★))  ((X′ ⇒ ★) ⇒ (X′ ⇒ ★))    │ │ λ♯0. □\n" ++
    "  │ │ ♯0                     (X ⇒ ★)              (Y ⇒ ★)              Y ≈ Y, ★⊑★                              (Y ⇒ ★)              (X′ ⇒ ★)                 │ │ ♯0\n" ++
    "  │ └ □ ↓ ⇒-con              (X ⇒ ★)              (Z ⇒ ★)              Z ≈ Z, ★⊑★ + matched conceal partner    (Z ⇒ ★)              (Y′ ⇒ ★)                 │ └ □ ↓ ⇒-con\n" ++
    "  │   □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                (★ ⇒ ★)              (★ ⇒ ★)                  │   □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │   □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                (★ ⇒ ★)              (★ ⇒ ★)                  │   □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │   λ♯0. □                 (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                (★ ⇒ ★)              (★ ⇒ ★)                  │   λ♯0. □\n" ++
    "  │   □₁ · □₂                ★                    ★                    ★⊑★                                     ★                    ★                        │   □₁ · □₂\n" ++
    "  │   ├ λ♯1. □               (★ ⇒ ★)              (★ ⇒ ★)              ★⊑★, ★⊑★                                (★ ⇒ ★)              (★ ⇒ ★)                  │   ├ λ♯1. □\n" ++
    "  │   │ ♯1                   ★                    ★                    ★⊑★                                     ★                    ★                        │   │ ♯1\n" ++
    "  │   └ □ ⟨ ℕ↦★ ⟩            ★                    ★                    ★⊑★                                     ★                    ★                        │   └ □ ⟨ ★↦★ ⟩\n" ++
    "  │     ♯0                   ℕ                    ℕ                    ι⊑★                                     ★                    ★                        │     ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩                ℕ                    ℕ                    ι⊑★                                     ★                    ★                        └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                       ℕ                    ℕ                    ℕ⊑ℕ                                     ℕ                    ℕ                          42"
checkpoint₅-ladder-pinned = refl
checkpoint₆-ladder-pinned :
  checkpoint₆-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                               ηᴿB      B         target term\n" ++
    "─────────────────────────  ───────  ───────  ────────────────────────────────────  ───────  ────────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                              (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                                   ★        ★           □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     ├ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ ↑ ⇒-rev              (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + matched reveal partner     (★ ⇒ ★)  (★ ⇒ ★)     │ □ ↑ ⇒-rev\n" ++
    "  │ ─                      (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + source rebase            (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↑ ⇒-rev\n" ++
    "  │ ─                      (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★ + source rebase            (Y ⇒ ★)  (X′ ⇒ ★)    │ □ ↓ ⇒-con\n" ++
    "  │ □ ↓ ⇒-con              (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + matched conceal partner  (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↓ ⇒-con\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                                   ★        ★           │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                                   ★        ★           │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                                   ★        ★           │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                                   ★        ★           │   ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩              ℕ        ℕ        ι⊑★                                   ★        ★           └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ             42"
checkpoint₆-ladder-pinned = refl
checkpoint₇-ladder-pinned :
  checkpoint₇-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                               ηᴿB      B         target term\n" ++
    "─────────────────────────  ───────  ───────  ────────────────────────────────────  ───────  ────────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                              (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                                   ★        ★           □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     ├ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ ↑ ⇒-rev              (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + matched reveal partner     (★ ⇒ ★)  (★ ⇒ ★)     │ □ ↑ ⇒-rev\n" ++
    "  │ ─                      (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + source rebase            (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↑ ⇒-rev\n" ++
    "  │ ─                      (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★ + source rebase            (Y ⇒ ★)  (X′ ⇒ ★)    │ □ ↓ ⇒-con\n" ++
    "  │ □ ↓ ⇒-con              (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + matched conceal partner  (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↓ ⇒-con\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                                   ★        ★           │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                                   ★        ★           │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                                   ★        ★           │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                                   ★        ★           │   ♯0\n" ++
    "  └ ─                      ℕ        ℕ        ι⊑★                                   ★        ★           └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ             42"
checkpoint₇-ladder-pinned = refl
checkpoint₈-ladder-pinned :
  checkpoint₈-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                               ηᴿB      B         target term\n" ++
    "─────────────────────────  ───────  ───────  ────────────────────────────────────  ───────  ────────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                              (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩                ★        ★        ★⊑★                                   ★        ★           □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                                   ★        ★           □₁ · □₂\n" ++
    "  ├ □ ↑ ⇒-rev              (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + matched reveal partner     (★ ⇒ ★)  (★ ⇒ ★)     ├ □ ↑ ⇒-rev\n" ++
    "  │ ─                      (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + source rebase            (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↑ ⇒-rev\n" ++
    "  │ ─                      (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★ + source rebase            (Y ⇒ ★)  (X′ ⇒ ★)    │ □ ↓ ⇒-con\n" ++
    "  │ □ ↓ ⇒-con              (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + matched conceal partner  (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↓ ⇒-con\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                                   ★        ★           │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                                   ★        ★           │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                                   ★        ★           │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                                   ★        ★           │   ♯0\n" ++
    "  └ ─                      ℕ        ℕ        ι⊑★                                   ★        ★           └ □ ⟨ ★↦★ ⟩\n" ++
    "    □ ⟨ ℕ↦ℕ ⟩              ℕ        ℕ        ι⊑★                                   ★        ★             □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ             42"
checkpoint₈-ladder-pinned = refl
checkpoint₉-ladder-pinned :
  checkpoint₉-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: X↦ℕ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                               ηᴿB      B         target term\n" ++
    "─────────────────────────  ───────  ───────  ────────────────────────────────────  ───────  ────────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                              (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩                ★        ★        ★⊑★                                   ★        ★           □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                                   ★        ★           □₁ · □₂\n" ++
    "  ├ □ ↑ ⇒-rev              (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + matched reveal partner     (★ ⇒ ★)  (★ ⇒ ★)     ├ □ ↑ ⇒-rev\n" ++
    "  │ ─                      (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + source rebase            (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↑ ⇒-rev\n" ++
    "  │ ─                      (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★ + source rebase            (Y ⇒ ★)  (X′ ⇒ ★)    │ □ ↓ ⇒-con\n" ++
    "  │ □ ↓ ⇒-con              (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + matched conceal partner  (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↓ ⇒-con\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                                   ★        ★           │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                                   ★        ★           │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                                   ★        ★           │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                                   ★        ★           │   ♯0\n" ++
    "  └ ─                      ℕ        ℕ        ι⊑★                                   ★        ★           └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ             42"
checkpoint₉-ladder-pinned = refl
checkpoint₁₀-ladder-pinned :
  checkpoint₁₀-ladder ≡
    "⟨X: ─ ⊑[X⊑★] ─ │ Y: X↦ℕ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                               ηᴿB      B         target term\n" ++
    "─────────────────────────  ───────  ───────  ────────────────────────────────────  ───────  ────────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                              (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)   ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ         └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩                ★        ★        ★⊑★                                   ★        ★           □ ⟨ ★↦★ ⟩\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent                ★        ★           □ ↑ id\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent                ★        ★           □ ↑ id\n" ++
    "  □ ↑ id                   ★        ★        ★⊑★ + generator absent                ★        ★           ─\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                                   ★        ★           □₁ · □₂\n" ++
    "  ├ ─                      (X ⇒ ★)  (Y ⇒ ★)  Y ≈ Y, ★⊑★ + source rebase            (Y ⇒ ★)  (X′ ⇒ ★)    ├ □ ↓ ⇒-con\n" ++
    "  │ □ ↓ ⇒-con              (X ⇒ ★)  (Z ⇒ ★)  Z ≈ Z, ★⊑★ + matched conceal partner  (Z ⇒ ★)  (Y′ ⇒ ★)    │ □ ↓ ⇒-con\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                                   ★        ★           │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                              (★ ⇒ ★)  (★ ⇒ ★)     │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                                   ★        ★           │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                                   ★        ★           │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                                   ★        ★           │   ♯0\n" ++
    "  └ ─                      X        Y        Y ≈ Y + source rebase                 Y        X′          └ □ ↓ seal X′\n" ++
    "    □ ↓ seal X             X        Z        Z ≈ Z + matched conceal partner       Z        Y′            □ ↓ seal Y′\n" ++
    "    ─                      ℕ        ℕ        ι⊑★                                   ★        ★             □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                                   ℕ        ℕ             42"
checkpoint₁₀-ladder-pinned = refl
checkpoint₁₁-ladder-pinned :
  checkpoint₁₁-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                            ηᴿB      B        target term\n" ++
    "─────────────────────────  ───────  ───────  ─────────────────────────────────  ───────  ───────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                           (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩                ★        ★        ★⊑★                                ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent             ★        ★          □ ↑ id\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent             ★        ★          □ ↑ id\n" ++
    "  □ ↑ id                   ★        ★        ★⊑★ + generator absent             ★        ★          ─\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent             ★        ★          □ ↓ id\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent             ★        ★          □ ↓ id\n" ++
    "  □ ↓ id                   ★        ★        ★⊑★ + generator absent             ★        ★          ─\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                                ★        ★          □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)    ├ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)    │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                                ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                                ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                                ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                                ★        ★          │   ♯0\n" ++
    "  └ □ ↑ unseal X           ℕ        ℕ        ι⊑★ + target unoccupied            ★        ★          └ ─\n" ++
    "    □ ↓ seal X             X        X        mark X⊑★ at X + target unoccupied  ★        ★            ─\n" ++
    "    ─                      ℕ        ℕ        ι⊑★                                ★        ★            □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ            42"
checkpoint₁₁-ladder-pinned = refl
checkpoint₁₂-ladder-pinned :
  checkpoint₁₂-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "─────────────────────────  ───────  ───────  ──────────────────────  ───────  ───────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩                ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  □ ↑ id                   ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  □ ↓ id                   ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                     ★        ★          □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    ├ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                     ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                     ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                     ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                     ★        ★          │   ♯0\n" ++
    "  └ ─                      ℕ        ℕ        ι⊑★                     ★        ★          └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ            42"
checkpoint₁₂-ladder-pinned = refl
checkpoint₁₃-ladder-pinned :
  checkpoint₁₃-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "─────────────────────────  ───────  ───────  ──────────────────────  ───────  ───────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩                ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  □ ↑ id                   ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  □ ↓ id                   ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ⟨ ★↦★ ⟩                ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                     ★        ★          □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    ├ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                     ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                     ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                     ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                     ★        ★          │   ♯0\n" ++
    "  └ ─                      ℕ        ℕ        ι⊑★                     ★        ★          └ □ ⟨ ★↦★ ⟩\n" ++
    "    □ ⟨ ℕ↦ℕ ⟩              ℕ        ℕ        ι⊑★                     ★        ★            □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ            42"
checkpoint₁₃-ladder-pinned = refl
checkpoint₁₄-ladder-pinned :
  checkpoint₁₄-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "─────────────────────────  ───────  ───────  ──────────────────────  ───────  ───────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩                ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  □ ↑ id                   ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  ─                        ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  □ ↓ id                   ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ⟨ ★↦★ ⟩                ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                     ★        ★          □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    ├ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                     ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                     ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                     ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                     ★        ★          │   ♯0\n" ++
    "  └ ─                      ℕ        ℕ        ι⊑★                     ★        ★          └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ            42"
checkpoint₁₄-ladder-pinned = refl
checkpoint₁₅-ladder-pinned :
  checkpoint₁₅-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term      A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "───────────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────────\n" ++
    "□₁ · □₂          ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0             ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩      ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩      ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─              ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  ─              ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  □ ↑ id         ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  ─              ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  ─              ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  □ ↓ id         ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ⟨ ★↦★ ⟩      ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩      ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂        ★        ★        ★⊑★                     ★        ★          □₁ · □₂\n" ++
    "  ├ λ♯0. □       (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    ├ λ♯0. □\n" ++
    "  │ □₁ · □₂      ★        ★        ★⊑★                     ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □     (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1         ★        ★        ★⊑★                     ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★                     ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0         ℕ        ℕ        ι⊑★                     ★        ★          │   ♯0\n" ++
    "  └ ─            ℕ        ℕ        ι⊑★                     ★        ★          └ □ ⟨ ★↦★ ⟩\n" ++
    "    □ ⟨ ℕ↦ℕ ⟩    ℕ        ℕ        ι⊑★                     ★        ★            □ ⟨ ℕ↦★ ⟩\n" ++
    "    42           ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ            42"
checkpoint₁₅-ladder-pinned = refl
checkpoint₁₆-ladder-pinned :
  checkpoint₁₆-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term      A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "───────────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────────\n" ++
    "□₁ · □₂          ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0             ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩      ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩      ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─              ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  ─              ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  □ ↑ id         ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  ─              ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  ─              ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  □ ↓ id         ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ⟨ ★↦★ ⟩      ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩      ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂        ★        ★        ★⊑★                     ★        ★          □₁ · □₂\n" ++
    "  ├ λ♯0. □       (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    ├ λ♯0. □\n" ++
    "  │ □₁ · □₂      ★        ★        ★⊑★                     ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □     (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1         ★        ★        ★⊑★                     ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★                     ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0         ℕ        ℕ        ι⊑★                     ★        ★          │   ♯0\n" ++
    "  └ ─            ℕ        ℕ        ι⊑★                     ★        ★          └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42           ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ            42"
checkpoint₁₆-ladder-pinned = refl
checkpoint₁₇-ladder-pinned :
  checkpoint₁₇-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term    A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "─────────────  ───────  ───────  ──────────────────────  ───────  ───────  ─────────────\n" ++
    "□₁ · □₂        ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □       (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0           ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩    ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩    ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─            ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  ─            ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  □ ↑ id       ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  ─            ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  ─            ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  □ ↓ id       ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ⟨ ★↦★ ⟩    ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩    ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂      ★        ★        ★⊑★                     ★        ★          □₁ · □₂\n" ++
    "  ├ λ♯0. □     (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    ├ λ♯0. □\n" ++
    "  │ ♯0         ★        ★        ★⊑★                     ★        ★          │ ♯0\n" ++
    "  └ ─          ★        ★        ★⊑★                     ★        ★          └ □ ⟨ ★↦★ ⟩\n" ++
    "    □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★                     ★        ★            □ ⟨ ℕ↦★ ⟩\n" ++
    "    42         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ            42"
checkpoint₁₇-ladder-pinned = refl
checkpoint₁₈-ladder-pinned :
  checkpoint₁₈-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩  ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  □ ↑ id     ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  □ ↓ id     ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ⟨ ★↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ          42"
checkpoint₁₈-ladder-pinned = refl
checkpoint₁₉-ladder-pinned :
  checkpoint₁₉-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩  ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  □ ↑ id     ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  □ ↓ id     ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ⟨ ★↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ          42"
checkpoint₁₉-ladder-pinned = refl
checkpoint₂₀-ladder-pinned :
  checkpoint₂₀-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩  ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  □ ↑ id     ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  □ ↓ id     ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ          42"
checkpoint₂₀-ladder-pinned = refl
checkpoint₂₁-ladder-pinned :
  checkpoint₂₁-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩  ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  □ ↑ id     ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↓ id\n" ++
    "  □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ          42"
checkpoint₂₁-ladder-pinned = refl
checkpoint₂₂-ladder-pinned :
  checkpoint₂₂-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩  ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ★↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  ─          ★        ★        ★⊑★ + generator absent  ★        ★          □ ↑ id\n" ++
    "  □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ          42"
checkpoint₂₂-ladder-pinned = refl
checkpoint₂₃-ladder-pinned :
  checkpoint₂₃-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs   ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩  ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  ─          ★        ★        ★⊑★       ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★       ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42         ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ          42"
checkpoint₂₃-ladder-pinned = refl
checkpoint₂₄-ladder-pinned :
  checkpoint₂₄-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs   ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        │ ♯0\n" ++
    "└ 42         ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        └ 42"
checkpoint₂₄-ladder-pinned = refl
checkpoint₂₅-ladder-pinned :
  checkpoint₂₅-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─ │ Y: ─ ⊑[X⊑★] X′↦＇Y′ │ Z: ─ ⊑[X⊑★] Y′↦★⟩\n" ++
    "source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term\n" ++
    "───────────  ─  ───  ───────  ───  ─  ───────────\n" ++
    "42           ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  42"
checkpoint₂₅-ladder-pinned = refl
