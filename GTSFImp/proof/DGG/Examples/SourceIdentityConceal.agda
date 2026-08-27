{-# OPTIONS --safe #-}

module proof.DGG.Examples.SourceIdentityConceal where

-- File Charter:
--   * Checks a source-only higher-order instantiation whose generated
--     function conceal has an active domain and a structural-identity result.
--   * Gives source typing and imprecision plus ordinary compiler outputs.
--   * Builds the executable traces before adding one CTI checkpoint after
--     every more-precise reduction.

import Data.Fin as Fin
open import Data.Bool using (false)
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
open import TyStore using (TyStore; store-empty; store-bind; _∋_⦂_; Z∋)
open import CastTerms using (Ctx; Term; ⟨_,_,_⟩; _,ˢ_; _⊢_⦂_)
import CastTerms as C
open import Compile using (compile)
open import Primitives using (κℕ)
import Conversion as Conv
open import Reduction using
  (bind; keep; applyConsistency; []; _∷_; _—↠[_]_; _—→[_]⟨_⟩_;
   _∎[])
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

ℓ-higher : Label
ℓ-higher = 1

ℓ-data : Label
ℓ-data = 2

ℓ-result : Label
ℓ-result = 3

more-precise : GTerm 0
more-precise =
  (ƛ ℕᵗ ⇒ ` 0) ·[ ℓ-result ]
    (((((Λ (ƛ X⇒★ ⇒ ` 0)) `[ ℕᵗ ]) ·[ ℓ-higher ]
      (ƛ ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      ·[ ℓ-data ] $ (κℕ 42)))

less-precise : GTerm 0
less-precise =
  (ƛ ℕᵗ ⇒ ` 0) ·[ ℓ-result ]
    ((((ƛ dynamic-function ⇒ ` 0) ·[ ℓ-higher ]
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

more-poly-⊢ :
  0 ∣ [] ⊢ᴳ Λ (ƛ X⇒★ ⇒ ` 0) ⦂ ∀higher-X
more-poly-⊢ =
  ⊢Λ {zero∈A = X∈higher-X}
    (ƛ X⇒★ ⇒ ` 0) (⊢ƛ (⊢` Z))

less-higher-⊢ :
  0 ∣ [] ⊢ᴳ (ƛ dynamic-function ⇒ ` 0) ⦂ higher-dynamic
less-higher-⊢ = ⊢ƛ (⊢` Z)

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

more-higher-core-⊢ :
  0 ∣ [] ⊢ᴳ
    (((Λ (ƛ X⇒★ ⇒ ` 0)) `[ ℕᵗ ]) ·[ ℓ-higher ]
      (ƛ ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
    ⦂ (ℕᵗ ⇒ ★)
more-higher-core-⊢ =
  ⊢· (⊢• more-poly-⊢) more-argument-⊢
    (id (‵ `ℕ) ↦ id ★)

less-higher-core-⊢ :
  0 ∣ [] ⊢ᴳ
    ((ƛ dynamic-function ⇒ ` 0) ·[ ℓ-higher ]
      (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
    ⦂ dynamic-function
less-higher-core-⊢ =
  ⊢· less-higher-⊢ less-argument-⊢ (id ★ ↦ id ★)

more-core-⊢ :
  0 ∣ [] ⊢ᴳ
    ((((Λ (ƛ X⇒★ ⇒ ` 0)) `[ ℕᵗ ]) ·[ ℓ-higher ]
      (ƛ ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      ·[ ℓ-data ] $ (κℕ 42)) ⦂ ★
more-core-⊢ =
  ⊢· more-higher-core-⊢ (⊢$ (κℕ 42)) (id (‵ `ℕ))

less-core-⊢ :
  0 ∣ [] ⊢ᴳ
    (((ƛ dynamic-function ⇒ ` 0) ·[ ℓ-higher ]
      (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      ·[ ℓ-data ] $ (κℕ 42)) ⦂ ★
less-core-⊢ =
  ⊢· less-higher-core-⊢ (⊢$ (κℕ 42)) (？ (id (‵ `ℕ)))

more-precise-⊢ : 0 ∣ [] ⊢ᴳ more-precise ⦂ ℕᵗ
more-precise-⊢ =
  ⊢· (⊢ƛ (⊢` Z)) more-core-⊢ nat-consistent-star

less-precise-⊢ : 0 ∣ [] ⊢ᴳ less-precise ⦂ ℕᵗ
less-precise-⊢ =
  ⊢· (⊢ƛ (⊢` Z)) less-core-⊢ nat-consistent-star

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
higher-ℕ⊑higher-dynamic = I.⇒⊑⇒ ℕ⇒★⊑★⇒★ ℕ⇒★⊑★⇒★

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

higher-function-imprecision :
  I.instᵐ (I.idᵐ {Δ = 0}) ∣ [] ⊢ᴳ²
    (ƛ X⇒★ ⇒ ` 0) ⊑ (ƛ dynamic-function ⇒ ` 0)
    ⦂ higher-X ⊑ higher-dynamic ∶ higher-X⊑higher-dynamic
higher-function-imprecision =
  GTI.ƛ⊑ƛᴳ
    (GTI.x⊑xᴳ GTI.Zⁱ)

poly-function-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ²
    Λ (ƛ X⇒★ ⇒ ` 0) ⊑ (ƛ dynamic-function ⇒ ` 0)
    ⦂ ∀higher-X ⊑ higher-dynamic ∶ ∀higher-X⊑higher-dynamic
poly-function-imprecision =
  GTI.Λ⊑ᴳ nonvar-fun X∈higher-X GTI.lift-[]
    (ƛ X⇒★ ⇒ ` 0) less-higher-⊢
    higher-function-imprecision

higher-core-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ²
    (((Λ (ƛ X⇒★ ⇒ ` 0)) `[ ℕᵗ ]) ·[ ℓ-higher ]
      (ƛ ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
    ⊑ ((ƛ dynamic-function ⇒ ` 0) ·[ ℓ-higher ]
      (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
    ⦂ (ℕᵗ ⇒ ★) ⊑ dynamic-function ∶ ℕ⇒★⊑★⇒★
higher-core-imprecision =
  GTI.·⊑·ᴳ
    (GTI.[]⊑ᴳ poly-function-imprecision I.ι⊑★
      (I.⇒⊑⇒ ℕ⇒★⊑★⇒★ ℕ⇒★⊑★⇒★))
    argument-imprecision
    (id (‵ `ℕ) ↦ id ★)
    (id ★ ↦ id ★)

core-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ²
    ((((Λ (ƛ X⇒★ ⇒ ` 0)) `[ ℕᵗ ]) ·[ ℓ-higher ]
      (ƛ ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      ·[ ℓ-data ] $ (κℕ 42))
    ⊑ (((ƛ dynamic-function ⇒ ` 0) ·[ ℓ-higher ]
      (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ ℓ-inner ] ` 0)))
      ·[ ℓ-data ] $ (κℕ 42))
    ⦂ ★ ⊑ ★ ∶ I.★⊑★
core-imprecision =
  GTI.·⊑·ᴳ
    higher-core-imprecision
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
-- Ordinary compiler outputs and executable result
------------------------------------------------------------------------

more-precise-compiled : Term 0
more-precise-compiled = proj₁ (compile {Σ = store-empty} more-precise-⊢)

more-precise-compiled-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ more-precise-compiled ⦂ ℕᵗ
more-precise-compiled-⊢ =
  proj₂ (compile {Σ = store-empty} more-precise-⊢)

less-precise-compiled : Term 0
less-precise-compiled = proj₁ (compile {Σ = store-empty} less-precise-⊢)

less-precise-compiled-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ less-precise-compiled ⦂ ℕᵗ
less-precise-compiled-⊢ =
  proj₂ (compile {Σ = store-empty} less-precise-⊢)

more-precise-eval :
  Ex.evalBlame Ex.gas more-precise-compiled-⊢ ≡ just false
more-precise-eval = refl

less-precise-eval :
  Ex.evalBlame Ex.gas less-precise-compiled-⊢ ≡ just false
less-precise-eval = refl


------------------------------------------------------------------------
-- Runtime world and generated conversions
------------------------------------------------------------------------

base-context : Ctx
base-context = ⟨ 0 , store-empty , [] ⟩

source-only-world : (base-context ,ˢ ℕᵗ) ⊑ᶜ base-context
source-only-world = bindLeftᶜ emptyᶜ ℕᵗ

source-member : store-bind store-empty ℕᵗ ∋ Fin.zero ⦂ ℕᵗ
source-member = Z∋ refl

source-higher-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    ((Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★) Conv.↦↑
      (Conv.seal Fin.zero ℕᵗ Conv.↦↑ Conv.id↑ ★))
source-higher-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-⇒
      (Conv.⊢↑-unseal source-member)
      (Conv.⊢↓-id-star source-member))
    (Conv.⊢↑-⇒
      (Conv.⊢↓-seal source-member)
      (Conv.⊢↑-id-star source-member))

source-function-conceal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↓[ Fin.zero ⦂ ℕᵗ ]
    (Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★)
source-function-conceal⊢ =
  Conv.⊢↓-⇒
    (Conv.⊢↑-unseal source-member)
    (Conv.⊢↓-id-star source-member)

source-arrow-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    (Conv.seal Fin.zero ℕᵗ Conv.↦↑ Conv.id↑ ★)
source-arrow-reveal⊢ =
  Conv.⊢↑-⇒
    (Conv.⊢↓-seal source-member)
    (Conv.⊢↑-id-star source-member)

source-seal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↓[ Fin.zero ⦂ ℕᵗ ]
    Conv.seal Fin.zero ℕᵗ
source-seal⊢ = Conv.⊢↓-seal source-member

source-unseal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ]
    Conv.unseal Fin.zero ℕᵗ
source-unseal⊢ = Conv.⊢↑-unseal source-member

source-identity-conceal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↓[ Fin.zero ⦂ ℕᵗ ] Conv.id↓ ★
source-identity-conceal⊢ = Conv.⊢↓-id-star source-member

source-identity-reveal⊢ :
  store-bind store-empty ℕᵗ Conv.⊢↑[ Fin.zero ⦂ ℕᵗ ] Conv.id↑ ★
source-identity-reveal⊢ = Conv.⊢↑-id-star source-member

source-unoccupied : ∀ Xᴿ
  → toRenameᵗ (ηᴿᶜ source-only-world) Xᴿ
    ≢ toRenameᵗ (ηᴸᶜ source-only-world) Fin.zero
source-unoccupied ()

source-higher-reveal-active :
  revealGeneratorPosition source-higher-reveal⊢ ≢ generator-absent
source-higher-reveal-active ()

source-function-conceal-active :
  concealGeneratorPosition source-function-conceal⊢ ≢ generator-absent
source-function-conceal-active ()

source-arrow-reveal-active :
  revealGeneratorPosition source-arrow-reveal⊢ ≢ generator-absent
source-arrow-reveal-active ()

source-seal-active :
  concealGeneratorPosition source-seal⊢ ≢ generator-absent
source-seal-active ()

source-unseal-active :
  revealGeneratorPosition source-unseal⊢ ≢ generator-absent
source-unseal-active ()

source-identity-conceal-absent :
  concealGeneratorPosition source-identity-conceal⊢ ≡ generator-absent
source-identity-conceal-absent = refl

source-identity-reveal-absent :
  revealGeneratorPosition source-identity-reveal⊢ ≡ generator-absent
source-identity-reveal-absent = refl

source-shifted-id-result :
  renameEnv∼ (Consistency.skip id↪ᵗ) (idᶜ {Δ = 0}) ⊢ ★ ∼ ★
source-shifted-id-result = id ★

source-shifted-id-argument :
  flipᵐ (renameEnv∼ (Consistency.skip id↪ᵗ)
    (idᶜ {Δ = 0})) ⊢ ℕᵗ ∼ ℕᵗ
source-shifted-id-argument = id (‵ `ℕ)


------------------------------------------------------------------------
-- Initial cast-term imprecision
------------------------------------------------------------------------

less-higher-compiled-⊢ :
  base-context ⊢ C.ƛ (C.` 0) ⦂ higher-dynamic
less-higher-compiled-⊢ =
  proj₂ (compile {Σ = store-empty} less-higher-⊢)

lifted-higher-function-imprecision :
  liftLeftᶜ emptyᶜ CTI.⊢²
    C.ƛ (C.` 0) ⊑ C.ƛ (C.` 0) ∶ higher-X⊑higher-dynamic
lifted-higher-function-imprecision =
  CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = X⇒★⊑★⇒★} Z Z)

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
  emptyᶜ CTI.⊢² more-precise-compiled ⊑ less-precise-compiled ∶ I.ι⊑ι
checkpoint₀-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (？ (id {μ = idᶜ} (‵ `ℕ)))
      (？ (id {μ = idᶜ} (‵ `ℕ)))
      (CTI.·⊑·²
        {pA = I.ι⊑★}
        {pB = I.★⊑★}
        (CTI.·⊑·²
          {pA = ℕ⇒★⊑★⇒★}
          {pB = ℕ⇒★⊑★⇒★}
          (CTI.•⊑²
            ∀higher-X⊑higher-dynamic
            (CTI.Λ⊑²
              nonvar-fun
              X∈higher-X
              (C.ƛ (C.` 0))
              less-higher-compiled-⊢
              lifted-higher-function-imprecision
              ∀higher-X⊑higher-dynamic)
            I.ι⊑★
            higher-ℕ⊑higher-dynamic)
          (CTI.cast⊑cast²
            (id {μ = idᶜ} (‵ `ℕ) ↦ id ★)
            (id {μ = idᶜ} ★ ↦ id ★)
            initial-argument-imprecision
            ℕ⇒★⊑★⇒★))
        (CTI.cast⊑cast²
          (id {μ = idᶜ} (‵ `ℕ))
          (id {μ = idᶜ} (‵ `ℕ) !)
          (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
          I.ι⊑★))
      I.ι⊑ι)

checkpoint₀-ladder : String
checkpoint₀-ladder = impLadderDefault checkpoint₀-imprecision

allocated-higher-function-imprecision :
  source-only-world CTI.⊢²
    C.ƛ (C.` 0) ⊑ C.ƛ (C.` 0) ∶ higher-X⊑higher-dynamic
allocated-higher-function-imprecision =
  CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = X⇒★⊑★⇒★} Z Z)

source-higher-function-imprecision :
  source-only-world CTI.⊢²
    (C.ƛ (C.` 0)) C.↑
      ((Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★) Conv.↦↑
        (Conv.seal Fin.zero ℕᵗ Conv.↦↑ Conv.id↑ ★))
    ⊑ C.ƛ (C.` 0) ∶ higher-ℕ⊑higher-dynamic
source-higher-function-imprecision =
  CTI.reveal⊑-only²
    source-higher-reveal⊢
    source-higher-reveal-active
    refl
    source-unoccupied
    I.ι⊑★
    allocated-higher-function-imprecision
    higher-ℕ⊑higher-dynamic

allocated-argument-imprecision :
  source-only-world CTI.⊢²
    C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ renameᵐᶜ (Consistency.skip id↪ᵗ)
        (symᶜ star-consistent-nat) ⟩))
    ⊑ C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ symᶜ (id {μ = idᶜ} ★) ⟩)) ∶ ℕ⇒★⊑★⇒★
allocated-argument-imprecision =
  CTI.ƛ⊑ƛ²
    (CTI.·⊑·²
      (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
        (CTI.x⊑x² {p = I.★⊑★} Z Z))
      (CTI.cast⊑cast²
        (renameᵐᶜ (Consistency.skip id↪ᵗ)
          (symᶜ star-consistent-nat))
        (symᶜ (id {μ = idᶜ} ★))
        (CTI.x⊑x² {p = I.ι⊑★} Z Z)
        I.★⊑★))

initial-data-imprecision :
  source-only-world CTI.⊢²
    C.$ (κℕ 42) C.⟨ renameᵐᶜ (Consistency.skip id↪ᵗ)
      (symᶜ (id {μ = idᶜ} (‵ `ℕ))) ⟩
    ⊑ C.$ (κℕ 42) C.⟨ symᶜ (？ (id {μ = idᶜ} (‵ `ℕ))) ⟩
      ∶ I.ι⊑★
initial-data-imprecision =
  CTI.cast⊑cast²
    (renameᵐᶜ (Consistency.skip id↪ᵗ)
      (symᶜ (id {μ = idᶜ} (‵ `ℕ))))
    (symᶜ (？ (id {μ = idᶜ} (‵ `ℕ))))
    (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
    I.ι⊑★

------------------------------------------------------------------------
-- Operational checkpoints
------------------------------------------------------------------------

more-checkpoint₀ : Term 0
more-checkpoint₀ = more-precise-compiled

more-store₀ : TyStore 0
more-store₀ = store-empty

more-step₀ : Step.OneStep more-store₀ more-checkpoint₀
more-step₀ =
  Step.from-just-step (step? more-store₀ more-checkpoint₀) refl

more-checkpoint₁ : Term (Step.Δ′ more-step₀)
more-checkpoint₁ = Step.next more-step₀

more-store₁ : TyStore (Step.Δ′ more-step₀)
more-store₁ = Step.store-after more-step₀

more-step₁ : Step.OneStep more-store₁ more-checkpoint₁
more-step₁ =
  Step.from-just-step (step? more-store₁ more-checkpoint₁) refl

more-checkpoint₂ : Term (Step.Δ′ more-step₁)
more-checkpoint₂ = Step.next more-step₁

more-store₂ : TyStore (Step.Δ′ more-step₁)
more-store₂ = Step.store-after more-step₁

more-step₂ : Step.OneStep more-store₂ more-checkpoint₂
more-step₂ =
  Step.from-just-step (step? more-store₂ more-checkpoint₂) refl

more-checkpoint₃ : Term (Step.Δ′ more-step₂)
more-checkpoint₃ = Step.next more-step₂

more-store₃ : TyStore (Step.Δ′ more-step₂)
more-store₃ = Step.store-after more-step₂

more-step₃ : Step.OneStep more-store₃ more-checkpoint₃
more-step₃ =
  Step.from-just-step (step? more-store₃ more-checkpoint₃) refl

more-checkpoint₄ : Term (Step.Δ′ more-step₃)
more-checkpoint₄ = Step.next more-step₃

more-store₄ : TyStore (Step.Δ′ more-step₃)
more-store₄ = Step.store-after more-step₃

more-step₄ : Step.OneStep more-store₄ more-checkpoint₄
more-step₄ =
  Step.from-just-step (step? more-store₄ more-checkpoint₄) refl

more-checkpoint₅ : Term (Step.Δ′ more-step₄)
more-checkpoint₅ = Step.next more-step₄

more-store₅ : TyStore (Step.Δ′ more-step₄)
more-store₅ = Step.store-after more-step₄

more-step₅ : Step.OneStep more-store₅ more-checkpoint₅
more-step₅ =
  Step.from-just-step (step? more-store₅ more-checkpoint₅) refl

more-checkpoint₆ : Term (Step.Δ′ more-step₅)
more-checkpoint₆ = Step.next more-step₅

more-store₆ : TyStore (Step.Δ′ more-step₅)
more-store₆ = Step.store-after more-step₅

more-step₆ : Step.OneStep more-store₆ more-checkpoint₆
more-step₆ =
  Step.from-just-step (step? more-store₆ more-checkpoint₆) refl

more-checkpoint₇ : Term (Step.Δ′ more-step₆)
more-checkpoint₇ = Step.next more-step₆

more-store₇ : TyStore (Step.Δ′ more-step₆)
more-store₇ = Step.store-after more-step₆

more-step₇ : Step.OneStep more-store₇ more-checkpoint₇
more-step₇ =
  Step.from-just-step (step? more-store₇ more-checkpoint₇) refl

more-checkpoint₈ : Term (Step.Δ′ more-step₇)
more-checkpoint₈ = Step.next more-step₇

more-store₈ : TyStore (Step.Δ′ more-step₇)
more-store₈ = Step.store-after more-step₇

more-step₈ : Step.OneStep more-store₈ more-checkpoint₈
more-step₈ =
  Step.from-just-step (step? more-store₈ more-checkpoint₈) refl

more-checkpoint₉ : Term (Step.Δ′ more-step₈)
more-checkpoint₉ = Step.next more-step₈

more-store₉ : TyStore (Step.Δ′ more-step₈)
more-store₉ = Step.store-after more-step₈

more-step₉ : Step.OneStep more-store₉ more-checkpoint₉
more-step₉ =
  Step.from-just-step (step? more-store₉ more-checkpoint₉) refl

more-checkpoint₁₀ : Term (Step.Δ′ more-step₉)
more-checkpoint₁₀ = Step.next more-step₉

more-store₁₀ : TyStore (Step.Δ′ more-step₉)
more-store₁₀ = Step.store-after more-step₉

more-step₁₀ : Step.OneStep more-store₁₀ more-checkpoint₁₀
more-step₁₀ =
  Step.from-just-step (step? more-store₁₀ more-checkpoint₁₀) refl

more-checkpoint₁₁ : Term (Step.Δ′ more-step₁₀)
more-checkpoint₁₁ = Step.next more-step₁₀

more-store₁₁ : TyStore (Step.Δ′ more-step₁₀)
more-store₁₁ = Step.store-after more-step₁₀

more-step₁₁ : Step.OneStep more-store₁₁ more-checkpoint₁₁
more-step₁₁ =
  Step.from-just-step (step? more-store₁₁ more-checkpoint₁₁) refl

more-checkpoint₁₂ : Term (Step.Δ′ more-step₁₁)
more-checkpoint₁₂ = Step.next more-step₁₁

more-store₁₂ : TyStore (Step.Δ′ more-step₁₁)
more-store₁₂ = Step.store-after more-step₁₁

more-step₁₂ : Step.OneStep more-store₁₂ more-checkpoint₁₂
more-step₁₂ =
  Step.from-just-step (step? more-store₁₂ more-checkpoint₁₂) refl

more-checkpoint₁₃ : Term (Step.Δ′ more-step₁₂)
more-checkpoint₁₃ = Step.next more-step₁₂

more-store₁₃ : TyStore (Step.Δ′ more-step₁₂)
more-store₁₃ = Step.store-after more-step₁₂

more-step₁₃ : Step.OneStep more-store₁₃ more-checkpoint₁₃
more-step₁₃ =
  Step.from-just-step (step? more-store₁₃ more-checkpoint₁₃) refl

more-checkpoint₁₄ : Term (Step.Δ′ more-step₁₃)
more-checkpoint₁₄ = Step.next more-step₁₃

more-store₁₄ : TyStore (Step.Δ′ more-step₁₃)
more-store₁₄ = Step.store-after more-step₁₃

more-step₁₄ : Step.OneStep more-store₁₄ more-checkpoint₁₄
more-step₁₄ =
  Step.from-just-step (step? more-store₁₄ more-checkpoint₁₄) refl

more-checkpoint₁₅ : Term (Step.Δ′ more-step₁₄)
more-checkpoint₁₅ = Step.next more-step₁₄

more-store₁₅ : TyStore (Step.Δ′ more-step₁₄)
more-store₁₅ = Step.store-after more-step₁₄

more-step₁₅ : Step.OneStep more-store₁₅ more-checkpoint₁₅
more-step₁₅ =
  Step.from-just-step (step? more-store₁₅ more-checkpoint₁₅) refl

more-checkpoint₁₆ : Term (Step.Δ′ more-step₁₅)
more-checkpoint₁₆ = Step.next more-step₁₅

more-store₁₆ : TyStore (Step.Δ′ more-step₁₅)
more-store₁₆ = Step.store-after more-step₁₅

------------------------------------------------------------------------
-- Less-precise executable trace
------------------------------------------------------------------------

less-checkpoint-raw₀ : Term 0
less-checkpoint-raw₀ = less-precise-compiled

less-store-raw₀ : TyStore 0
less-store-raw₀ = store-empty

less-step-raw₀ : Step.OneStep less-store-raw₀ less-checkpoint-raw₀
less-step-raw₀ =
  Step.from-just-step
    (step? less-store-raw₀ less-checkpoint-raw₀) refl

less-checkpoint-raw₁ : Term (Step.Δ′ less-step-raw₀)
less-checkpoint-raw₁ = Step.next less-step-raw₀

less-store-raw₁ : TyStore (Step.Δ′ less-step-raw₀)
less-store-raw₁ = Step.store-after less-step-raw₀

less-step-raw₁ : Step.OneStep less-store-raw₁ less-checkpoint-raw₁
less-step-raw₁ =
  Step.from-just-step
    (step? less-store-raw₁ less-checkpoint-raw₁) refl

less-checkpoint-raw₂ : Term (Step.Δ′ less-step-raw₁)
less-checkpoint-raw₂ = Step.next less-step-raw₁

less-store-raw₂ : TyStore (Step.Δ′ less-step-raw₁)
less-store-raw₂ = Step.store-after less-step-raw₁

less-step-raw₂ : Step.OneStep less-store-raw₂ less-checkpoint-raw₂
less-step-raw₂ =
  Step.from-just-step
    (step? less-store-raw₂ less-checkpoint-raw₂) refl

less-checkpoint-raw₃ : Term (Step.Δ′ less-step-raw₂)
less-checkpoint-raw₃ = Step.next less-step-raw₂

less-store-raw₃ : TyStore (Step.Δ′ less-step-raw₂)
less-store-raw₃ = Step.store-after less-step-raw₂

less-step-raw₃ : Step.OneStep less-store-raw₃ less-checkpoint-raw₃
less-step-raw₃ =
  Step.from-just-step
    (step? less-store-raw₃ less-checkpoint-raw₃) refl

less-checkpoint-raw₄ : Term (Step.Δ′ less-step-raw₃)
less-checkpoint-raw₄ = Step.next less-step-raw₃

less-store-raw₄ : TyStore (Step.Δ′ less-step-raw₃)
less-store-raw₄ = Step.store-after less-step-raw₃

less-step-raw₄ : Step.OneStep less-store-raw₄ less-checkpoint-raw₄
less-step-raw₄ =
  Step.from-just-step
    (step? less-store-raw₄ less-checkpoint-raw₄) refl

less-checkpoint-raw₅ : Term (Step.Δ′ less-step-raw₄)
less-checkpoint-raw₅ = Step.next less-step-raw₄

less-store-raw₅ : TyStore (Step.Δ′ less-step-raw₄)
less-store-raw₅ = Step.store-after less-step-raw₄

less-step-raw₅ : Step.OneStep less-store-raw₅ less-checkpoint-raw₅
less-step-raw₅ =
  Step.from-just-step
    (step? less-store-raw₅ less-checkpoint-raw₅) refl

less-checkpoint-raw₆ : Term (Step.Δ′ less-step-raw₅)
less-checkpoint-raw₆ = Step.next less-step-raw₅

less-store-raw₆ : TyStore (Step.Δ′ less-step-raw₅)
less-store-raw₆ = Step.store-after less-step-raw₅

less-step-raw₆ : Step.OneStep less-store-raw₆ less-checkpoint-raw₆
less-step-raw₆ =
  Step.from-just-step
    (step? less-store-raw₆ less-checkpoint-raw₆) refl

less-checkpoint-raw₇ : Term (Step.Δ′ less-step-raw₆)
less-checkpoint-raw₇ = Step.next less-step-raw₆

less-store-raw₇ : TyStore (Step.Δ′ less-step-raw₆)
less-store-raw₇ = Step.store-after less-step-raw₆

less-step-raw₇ : Step.OneStep less-store-raw₇ less-checkpoint-raw₇
less-step-raw₇ =
  Step.from-just-step
    (step? less-store-raw₇ less-checkpoint-raw₇) refl

less-checkpoint-raw₈ : Term (Step.Δ′ less-step-raw₇)
less-checkpoint-raw₈ = Step.next less-step-raw₇

less-store-raw₈ : TyStore (Step.Δ′ less-step-raw₇)
less-store-raw₈ = Step.store-after less-step-raw₇

less-step-raw₈ : Step.OneStep less-store-raw₈ less-checkpoint-raw₈
less-step-raw₈ =
  Step.from-just-step
    (step? less-store-raw₈ less-checkpoint-raw₈) refl

less-checkpoint-raw₉ : Term (Step.Δ′ less-step-raw₈)
less-checkpoint-raw₉ = Step.next less-step-raw₈

less-store-raw₉ : TyStore (Step.Δ′ less-step-raw₈)
less-store-raw₉ = Step.store-after less-step-raw₈


------------------------------------------------------------------------
-- Paired checkpoints
------------------------------------------------------------------------

less-checkpoint₀ = less-checkpoint-raw₀
less-checkpoint₁ = less-checkpoint-raw₀
less-checkpoint₂ = less-checkpoint-raw₀
less-checkpoint₃ = less-checkpoint-raw₁
less-checkpoint₄ = less-checkpoint-raw₁
less-checkpoint₅ = less-checkpoint-raw₂
less-checkpoint₆ = less-checkpoint-raw₂
less-checkpoint₇ = less-checkpoint-raw₂
less-checkpoint₈ = less-checkpoint-raw₂
less-checkpoint₉ = less-checkpoint-raw₃
less-checkpoint₁₀ = less-checkpoint-raw₄
less-checkpoint₁₁ = less-checkpoint-raw₆
less-checkpoint₁₂ = less-checkpoint-raw₇
less-checkpoint₁₃ = less-checkpoint-raw₇
less-checkpoint₁₄ = less-checkpoint-raw₇
less-checkpoint₁₅ = less-checkpoint-raw₈
less-checkpoint₁₆ = less-checkpoint-raw₉

more-final : more-checkpoint₁₆ ≡ C.$ (κℕ 42)
more-final = refl

less-final : less-checkpoint₁₆ ≡ C.$ (κℕ 42)
less-final = refl


------------------------------------------------------------------------
-- Whole-term reduction segments
------------------------------------------------------------------------

more-checkpoint₀↠₁ :
  more-checkpoint₀ —↠[ bind ℕᵗ ∷ [] ] more-checkpoint₁
more-checkpoint₀↠₁ =
  more-checkpoint₀
  —→[ bind ℕᵗ ]⟨ Step.reduction more-step₀ ⟩
  more-checkpoint₁ ∎[]

more-checkpoint₁↠₂ :
  more-checkpoint₁ —↠[ keep ∷ [] ] more-checkpoint₂
more-checkpoint₁↠₂ =
  more-checkpoint₁
  —→[ keep ]⟨ Step.reduction more-step₁ ⟩
  more-checkpoint₂ ∎[]

more-checkpoint₂↠₃ :
  more-checkpoint₂ —↠[ keep ∷ [] ] more-checkpoint₃
more-checkpoint₂↠₃ =
  more-checkpoint₂
  —→[ keep ]⟨ Step.reduction more-step₂ ⟩
  more-checkpoint₃ ∎[]

more-checkpoint₃↠₄ :
  more-checkpoint₃ —↠[ keep ∷ [] ] more-checkpoint₄
more-checkpoint₃↠₄ =
  more-checkpoint₃
  —→[ keep ]⟨ Step.reduction more-step₃ ⟩
  more-checkpoint₄ ∎[]

more-checkpoint₄↠₅ :
  more-checkpoint₄ —↠[ keep ∷ [] ] more-checkpoint₅
more-checkpoint₄↠₅ =
  more-checkpoint₄
  —→[ keep ]⟨ Step.reduction more-step₄ ⟩
  more-checkpoint₅ ∎[]

more-checkpoint₅↠₆ :
  more-checkpoint₅ —↠[ keep ∷ [] ] more-checkpoint₆
more-checkpoint₅↠₆ =
  more-checkpoint₅
  —→[ keep ]⟨ Step.reduction more-step₅ ⟩
  more-checkpoint₆ ∎[]

more-checkpoint₆↠₇ :
  more-checkpoint₆ —↠[ keep ∷ [] ] more-checkpoint₇
more-checkpoint₆↠₇ =
  more-checkpoint₆
  —→[ keep ]⟨ Step.reduction more-step₆ ⟩
  more-checkpoint₇ ∎[]

more-checkpoint₇↠₈ :
  more-checkpoint₇ —↠[ keep ∷ [] ] more-checkpoint₈
more-checkpoint₇↠₈ =
  more-checkpoint₇
  —→[ keep ]⟨ Step.reduction more-step₇ ⟩
  more-checkpoint₈ ∎[]

more-checkpoint₈↠₉ :
  more-checkpoint₈ —↠[ keep ∷ [] ] more-checkpoint₉
more-checkpoint₈↠₉ =
  more-checkpoint₈
  —→[ keep ]⟨ Step.reduction more-step₈ ⟩
  more-checkpoint₉ ∎[]

more-checkpoint₉↠₁₀ :
  more-checkpoint₉ —↠[ keep ∷ [] ] more-checkpoint₁₀
more-checkpoint₉↠₁₀ =
  more-checkpoint₉
  —→[ keep ]⟨ Step.reduction more-step₉ ⟩
  more-checkpoint₁₀ ∎[]

more-checkpoint₁₀↠₁₁ :
  more-checkpoint₁₀ —↠[ keep ∷ [] ] more-checkpoint₁₁
more-checkpoint₁₀↠₁₁ =
  more-checkpoint₁₀
  —→[ keep ]⟨ Step.reduction more-step₁₀ ⟩
  more-checkpoint₁₁ ∎[]

more-checkpoint₁₁↠₁₂ :
  more-checkpoint₁₁ —↠[ keep ∷ [] ] more-checkpoint₁₂
more-checkpoint₁₁↠₁₂ =
  more-checkpoint₁₁
  —→[ keep ]⟨ Step.reduction more-step₁₁ ⟩
  more-checkpoint₁₂ ∎[]

more-checkpoint₁₂↠₁₃ :
  more-checkpoint₁₂ —↠[ keep ∷ [] ] more-checkpoint₁₃
more-checkpoint₁₂↠₁₃ =
  more-checkpoint₁₂
  —→[ keep ]⟨ Step.reduction more-step₁₂ ⟩
  more-checkpoint₁₃ ∎[]

more-checkpoint₁₃↠₁₄ :
  more-checkpoint₁₃ —↠[ keep ∷ [] ] more-checkpoint₁₄
more-checkpoint₁₃↠₁₄ =
  more-checkpoint₁₃
  —→[ keep ]⟨ Step.reduction more-step₁₃ ⟩
  more-checkpoint₁₄ ∎[]

more-checkpoint₁₄↠₁₅ :
  more-checkpoint₁₄ —↠[ keep ∷ [] ] more-checkpoint₁₅
more-checkpoint₁₄↠₁₅ =
  more-checkpoint₁₄
  —→[ keep ]⟨ Step.reduction more-step₁₄ ⟩
  more-checkpoint₁₅ ∎[]

more-checkpoint₁₅↠₁₆ :
  more-checkpoint₁₅ —↠[ keep ∷ [] ] more-checkpoint₁₆
more-checkpoint₁₅↠₁₆ =
  more-checkpoint₁₅
  —→[ keep ]⟨ Step.reduction more-step₁₅ ⟩
  more-checkpoint₁₆ ∎[]

less-checkpoint₀↠₁ :
  less-checkpoint₀ —↠[ [] ] less-checkpoint₁
less-checkpoint₀↠₁ =
  less-checkpoint₀
  ∎[]

less-checkpoint₁↠₂ :
  less-checkpoint₁ —↠[ [] ] less-checkpoint₂
less-checkpoint₁↠₂ =
  less-checkpoint₁
  ∎[]

less-checkpoint₂↠₃ :
  less-checkpoint₂ —↠[ keep ∷ [] ] less-checkpoint₃
less-checkpoint₂↠₃ =
  less-checkpoint₂
  —→[ keep ]⟨ Step.reduction less-step-raw₀ ⟩
  less-checkpoint₃
  ∎[]

less-checkpoint₃↠₄ :
  less-checkpoint₃ —↠[ [] ] less-checkpoint₄
less-checkpoint₃↠₄ =
  less-checkpoint₃
  ∎[]

less-checkpoint₄↠₅ :
  less-checkpoint₄ —↠[ keep ∷ [] ] less-checkpoint₅
less-checkpoint₄↠₅ =
  less-checkpoint₄
  —→[ keep ]⟨ Step.reduction less-step-raw₁ ⟩
  less-checkpoint₅
  ∎[]

less-checkpoint₅↠₆ :
  less-checkpoint₅ —↠[ [] ] less-checkpoint₆
less-checkpoint₅↠₆ =
  less-checkpoint₅
  ∎[]

less-checkpoint₆↠₇ :
  less-checkpoint₆ —↠[ [] ] less-checkpoint₇
less-checkpoint₆↠₇ =
  less-checkpoint₆
  ∎[]

less-checkpoint₇↠₈ :
  less-checkpoint₇ —↠[ [] ] less-checkpoint₈
less-checkpoint₇↠₈ =
  less-checkpoint₇
  ∎[]

less-checkpoint₈↠₉ :
  less-checkpoint₈ —↠[ keep ∷ [] ] less-checkpoint₉
less-checkpoint₈↠₉ =
  less-checkpoint₈
  —→[ keep ]⟨ Step.reduction less-step-raw₂ ⟩
  less-checkpoint₉
  ∎[]

less-checkpoint₉↠₁₀ :
  less-checkpoint₉ —↠[ keep ∷ [] ] less-checkpoint₁₀
less-checkpoint₉↠₁₀ =
  less-checkpoint₉
  —→[ keep ]⟨ Step.reduction less-step-raw₃ ⟩
  less-checkpoint₁₀
  ∎[]

less-checkpoint₁₀↠₁₁ :
  less-checkpoint₁₀ —↠[ keep ∷ keep ∷ [] ] less-checkpoint₁₁
less-checkpoint₁₀↠₁₁ =
  less-checkpoint₁₀
  —→[ keep ]⟨ Step.reduction less-step-raw₄ ⟩
  less-checkpoint-raw₅
  —→[ keep ]⟨ Step.reduction less-step-raw₅ ⟩
  less-checkpoint₁₁
  ∎[]

less-checkpoint₁₁↠₁₂ :
  less-checkpoint₁₁ —↠[ keep ∷ [] ] less-checkpoint₁₂
less-checkpoint₁₁↠₁₂ =
  less-checkpoint₁₁
  —→[ keep ]⟨ Step.reduction less-step-raw₆ ⟩
  less-checkpoint₁₂
  ∎[]

less-checkpoint₁₂↠₁₃ :
  less-checkpoint₁₂ —↠[ [] ] less-checkpoint₁₃
less-checkpoint₁₂↠₁₃ =
  less-checkpoint₁₂
  ∎[]

less-checkpoint₁₃↠₁₄ :
  less-checkpoint₁₃ —↠[ [] ] less-checkpoint₁₄
less-checkpoint₁₃↠₁₄ =
  less-checkpoint₁₃
  ∎[]

less-checkpoint₁₄↠₁₅ :
  less-checkpoint₁₄ —↠[ keep ∷ [] ] less-checkpoint₁₅
less-checkpoint₁₄↠₁₅ =
  less-checkpoint₁₄
  —→[ keep ]⟨ Step.reduction less-step-raw₇ ⟩
  less-checkpoint₁₅
  ∎[]

less-checkpoint₁₅↠₁₆ :
  less-checkpoint₁₅ —↠[ keep ∷ [] ] less-checkpoint₁₆
less-checkpoint₁₅↠₁₆ =
  less-checkpoint₁₅
  —→[ keep ]⟨ Step.reduction less-step-raw₈ ⟩
  less-checkpoint₁₆
  ∎[]




------------------------------------------------------------------------
-- Cast-term imprecision at every checkpoint
------------------------------------------------------------------------

checkpoint₁-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₁ ⊑ less-checkpoint₁ ∶ I.ι⊑ι
checkpoint₁-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.·⊑·²
        {pA = I.ι⊑★}
        {pB = I.★⊑★}
        (CTI.·⊑·²
          {pA = ℕ⇒★⊑★⇒★}
          {pB = ℕ⇒★⊑★⇒★}
          source-higher-function-imprecision
          (CTI.cast⊑cast²
            (renameᵐᶜ (Consistency.skip id↪ᵗ)
              (symᶜ (id {μ = idᶜ} (‵ `ℕ) ↦ id ★)))
            (symᶜ (id {μ = idᶜ} ★ ↦ id ★))
            allocated-argument-imprecision
            ℕ⇒★⊑★⇒★))
        initial-data-imprecision)
      I.ι⊑ι)

checkpoint₁-ladder : String
checkpoint₁-ladder = impLadderDefault checkpoint₁-imprecision

allocated-casted-argument-imprecision :
  source-only-world CTI.⊢²
    (C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ renameᵐᶜ (Consistency.skip id↪ᵗ)
        (symᶜ star-consistent-nat) ⟩))) C.⟨
      renameᵐᶜ (Consistency.skip id↪ᵗ)
        (symᶜ (id {μ = idᶜ} (‵ `ℕ) ↦ id ★)) ⟩
    ⊑ (C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ symᶜ (id {μ = idᶜ} ★) ⟩))) C.⟨
      symᶜ (id {μ = idᶜ} ★ ↦ id ★) ⟩
    ∶ ℕ⇒★⊑★⇒★
allocated-casted-argument-imprecision =
  CTI.cast⊑cast²
    (renameᵐᶜ (Consistency.skip id↪ᵗ)
      (symᶜ (id {μ = idᶜ} (‵ `ℕ) ↦ id ★)))
    (symᶜ (id {μ = idᶜ} ★ ↦ id ★))
    allocated-argument-imprecision
    ℕ⇒★⊑★⇒★

source-concealed-argument-imprecision :
  source-only-world CTI.⊢²
    ((C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ renameᵐᶜ (Consistency.skip id↪ᵗ)
        (symᶜ star-consistent-nat) ⟩))) C.⟨
      renameᵐᶜ (Consistency.skip id↪ᵗ)
        (symᶜ (id {μ = idᶜ} (‵ `ℕ) ↦ id ★)) ⟩) C.↓
      (Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★)
    ⊑ (C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ symᶜ (id {μ = idᶜ} ★) ⟩))) C.⟨
      symᶜ (id {μ = idᶜ} ★ ↦ id ★) ⟩
    ∶ X⇒★⊑★⇒★
source-concealed-argument-imprecision =
  CTI.conceal⊑-only²
    source-function-conceal⊢
    source-function-conceal-active
    refl
    source-unoccupied
    I.ι⊑★
    allocated-casted-argument-imprecision
    X⇒★⊑★⇒★

source-arrow-result-imprecision :
  source-only-world CTI.⊢²
    ((C.ƛ (C.` 0)) C.·
      ((C.ƛ ((C.ƛ (C.` 0)) C.·
        (C.` 0 C.⟨ renameᵐᶜ (Consistency.skip id↪ᵗ)
          (symᶜ star-consistent-nat) ⟩))) C.⟨
        renameᵐᶜ (Consistency.skip id↪ᵗ)
          (symᶜ (id {μ = idᶜ} (‵ `ℕ) ↦ id ★)) ⟩ C.↓
        (Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★))) C.↑
      (Conv.seal Fin.zero ℕᵗ Conv.↦↑ Conv.id↑ ★)
    ⊑ (C.ƛ (C.` 0)) C.·
      ((C.ƛ ((C.ƛ (C.` 0)) C.·
        (C.` 0 C.⟨ symᶜ (id {μ = idᶜ} ★) ⟩))) C.⟨
        symᶜ (id {μ = idᶜ} ★ ↦ id ★) ⟩)
    ∶ ℕ⇒★⊑★⇒★
source-arrow-result-imprecision =
  CTI.reveal⊑-only²
    source-arrow-reveal⊢
    source-arrow-reveal-active
    refl
    source-unoccupied
    I.ι⊑★
    (CTI.·⊑·²
      allocated-higher-function-imprecision
      source-concealed-argument-imprecision)
    ℕ⇒★⊑★⇒★

checkpoint₂-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₂ ⊑ less-checkpoint₂ ∶ I.ι⊑ι
checkpoint₂-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.·⊑·²
        source-arrow-result-imprecision
        initial-data-imprecision)
      I.ι⊑ι)

checkpoint₂-ladder : String
checkpoint₂-ladder = impLadderDefault checkpoint₂-imprecision

source-arrow-argument-imprecision :
  source-only-world CTI.⊢²
    (((C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ renameᵐᶜ (Consistency.skip id↪ᵗ)
        (symᶜ star-consistent-nat) ⟩))) C.⟨
      renameᵐᶜ (Consistency.skip id↪ᵗ)
        (symᶜ (id {μ = idᶜ} (‵ `ℕ) ↦ id ★)) ⟩) C.↓
      (Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★)) C.↑
      (Conv.seal Fin.zero ℕᵗ Conv.↦↑ Conv.id↑ ★)
    ⊑ (C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ symᶜ (id {μ = idᶜ} ★) ⟩))) C.⟨
      symᶜ (id {μ = idᶜ} ★ ↦ id ★) ⟩
    ∶ ℕ⇒★⊑★⇒★
source-arrow-argument-imprecision =
  CTI.reveal⊑-only²
    source-arrow-reveal⊢
    source-arrow-reveal-active
    refl
    source-unoccupied
    I.ι⊑★
    source-concealed-argument-imprecision
    ℕ⇒★⊑★⇒★

stripped-data-imprecision :
  source-only-world CTI.⊢²
    C.$ (κℕ 42)
    ⊑ C.$ (κℕ 42) C.⟨ symᶜ (？ (id {μ = idᶜ} (‵ `ℕ))) ⟩
      ∶ I.ι⊑★
stripped-data-imprecision =
  CTI.⊑cast²
    (symᶜ (？ (id {μ = idᶜ} (‵ `ℕ))))
    (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
    I.ι⊑★

checkpoint₃-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₃ ⊑ less-checkpoint₃ ∶ I.ι⊑ι
checkpoint₃-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.·⊑·²
        source-arrow-argument-imprecision
        initial-data-imprecision)
      I.ι⊑ι)

checkpoint₃-ladder : String
checkpoint₃-ladder = impLadderDefault checkpoint₃-imprecision

checkpoint₄-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₄ ⊑ less-checkpoint₄ ∶ I.ι⊑ι
checkpoint₄-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.·⊑·²
        source-arrow-argument-imprecision
        stripped-data-imprecision)
      I.ι⊑ι)

checkpoint₄-ladder : String
checkpoint₄-ladder = impLadderDefault checkpoint₄-imprecision

source-casted-argument-to-bare :
  source-only-world CTI.⊢²
    (C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ renameᵐᶜ (Consistency.skip id↪ᵗ)
        (symᶜ star-consistent-nat) ⟩))) C.⟨
      renameᵐᶜ (Consistency.skip id↪ᵗ)
        (symᶜ (id {μ = idᶜ} (‵ `ℕ) ↦ id ★)) ⟩
    ⊑ C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ symᶜ (id {μ = idᶜ} ★) ⟩))
    ∶ ℕ⇒★⊑★⇒★
source-casted-argument-to-bare =
  CTI.cast⊑²
    (renameᵐᶜ (Consistency.skip id↪ᵗ)
      (symᶜ (id {μ = idᶜ} (‵ `ℕ) ↦ id ★)))
    allocated-argument-imprecision
    ℕ⇒★⊑★⇒★

source-concealed-function-to-bare :
  source-only-world CTI.⊢²
    ((C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ renameᵐᶜ (Consistency.skip id↪ᵗ)
        (symᶜ star-consistent-nat) ⟩))) C.⟨
      renameᵐᶜ (Consistency.skip id↪ᵗ)
        (symᶜ (id {μ = idᶜ} (‵ `ℕ) ↦ id ★)) ⟩) C.↓
      (Conv.unseal Fin.zero ℕᵗ Conv.↦↓ Conv.id↓ ★)
    ⊑ C.ƛ ((C.ƛ (C.` 0)) C.·
      (C.` 0 C.⟨ symᶜ (id {μ = idᶜ} ★) ⟩))
    ∶ X⇒★⊑★⇒★
source-concealed-function-to-bare =
  CTI.conceal⊑-only²
    source-function-conceal⊢
    source-function-conceal-active
    refl
    source-unoccupied
    I.ι⊑★
    source-casted-argument-to-bare
    X⇒★⊑★⇒★

target-tagged-data-imprecision :
  source-only-world CTI.⊢²
    C.$ (κℕ 42)
    ⊑ (C.$ (κℕ 42) C.⟨
      symᶜ (？ (id {μ = idᶜ} (‵ `ℕ))) ⟩) C.⟨
      symᶜ (id {μ = idᶜ} ★) ⟩ ∶ I.ι⊑★
target-tagged-data-imprecision =
  CTI.⊑cast²
    (symᶜ (id {μ = idᶜ} ★))
    stripped-data-imprecision
    I.ι⊑★

sealed-data-imprecision :
  source-only-world CTI.⊢²
    C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ
    ⊑ (C.$ (κℕ 42) C.⟨
      symᶜ (？ (id {μ = idᶜ} (‵ `ℕ))) ⟩) C.⟨
      symᶜ (id {μ = idᶜ} ★) ⟩ ∶ I.X⊑★ refl
sealed-data-imprecision =
  CTI.conceal⊑-only²
    source-seal⊢
    source-seal-active
    refl
    source-unoccupied
    I.ι⊑★
    target-tagged-data-imprecision
    (I.X⊑★ refl)

checkpoint₅-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₅ ⊑ less-checkpoint₅ ∶ I.ι⊑ι
checkpoint₅-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.reveal⊑-identity
        source-identity-reveal⊢
        source-identity-reveal-absent
        (CTI.⊑cast²
          (symᶜ (id {μ = idᶜ} ★))
          (CTI.·⊑·²
            source-concealed-function-to-bare
            sealed-data-imprecision)
          I.★⊑★)
        I.★⊑★)
      I.ι⊑ι)

checkpoint₅-ladder : String
checkpoint₅-ladder = impLadderDefault checkpoint₅-imprecision

unsealed-data-imprecision :
  source-only-world CTI.⊢²
    (C.$ (κℕ 42) C.↓ Conv.seal Fin.zero ℕᵗ) C.↑
      Conv.unseal Fin.zero ℕᵗ
    ⊑ (C.$ (κℕ 42) C.⟨
      symᶜ (？ (id {μ = idᶜ} (‵ `ℕ))) ⟩) C.⟨
      symᶜ (id {μ = idᶜ} ★) ⟩ ∶ I.ι⊑★
unsealed-data-imprecision =
  CTI.reveal⊑-only²
    source-unseal⊢
    source-unseal-active
    refl
    source-unoccupied
    I.ι⊑★
    sealed-data-imprecision
    I.ι⊑★

checkpoint₆-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₆ ⊑ less-checkpoint₆ ∶ I.ι⊑ι
checkpoint₆-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.reveal⊑-identity
        source-identity-reveal⊢
        source-identity-reveal-absent
        (CTI.conceal⊑-identity
          source-identity-conceal⊢
          source-identity-conceal-absent
          (CTI.⊑cast²
            (symᶜ (id {μ = idᶜ} ★))
            (CTI.·⊑·²
              source-casted-argument-to-bare
              unsealed-data-imprecision)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      I.ι⊑ι)

checkpoint₆-ladder : String
checkpoint₆-ladder = impLadderDefault checkpoint₆-imprecision

checkpoint₇-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₇ ⊑ less-checkpoint₇ ∶ I.ι⊑ι
checkpoint₇-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.reveal⊑-identity
        source-identity-reveal⊢
        source-identity-reveal-absent
        (CTI.conceal⊑-identity
          source-identity-conceal⊢
          source-identity-conceal-absent
          (CTI.⊑cast²
            (symᶜ (id {μ = idᶜ} ★))
            (CTI.·⊑·²
              source-casted-argument-to-bare
              target-tagged-data-imprecision)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      I.ι⊑ι)

checkpoint₇-ladder : String
checkpoint₇-ladder = impLadderDefault checkpoint₇-imprecision

checkpoint₈-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₈ ⊑ less-checkpoint₈ ∶ I.ι⊑ι
checkpoint₈-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.reveal⊑-identity
        source-identity-reveal⊢
        source-identity-reveal-absent
        (CTI.conceal⊑-identity
          source-identity-conceal⊢
          source-identity-conceal-absent
          (CTI.cast⊑cast²
            source-shifted-id-result
            (symᶜ (id {μ = idᶜ} ★))
            (CTI.·⊑·²
              allocated-argument-imprecision
              (CTI.⊑cast²
                (symᶜ (id {μ = idᶜ} ★))
                (CTI.cast⊑cast²
                  source-shifted-id-argument
                  (symᶜ (？ (id {μ = idᶜ} (‵ `ℕ))))
                  (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
                  I.ι⊑★)
                I.ι⊑★))
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      I.ι⊑ι)

checkpoint₈-ladder : String
checkpoint₈-ladder = impLadderDefault checkpoint₈-imprecision

source-tagged-data-imprecision :
  source-only-world CTI.⊢²
    C.$ (κℕ 42) C.⟨ renameᵐᶜ (Consistency.skip id↪ᵗ)
      (symᶜ star-consistent-nat) ⟩
    ⊑ C.$ (κℕ 42) C.⟨
      symᶜ (？ (id {μ = idᶜ} (‵ `ℕ))) ⟩ ∶ I.★⊑★
source-tagged-data-imprecision =
  CTI.cast⊑cast²
    (renameᵐᶜ (Consistency.skip id↪ᵗ)
      (symᶜ star-consistent-nat))
    (symᶜ (？ (id {μ = idᶜ} (‵ `ℕ))))
    (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)
    I.★⊑★

checkpoint₉-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₉ ⊑ less-checkpoint₉ ∶ I.ι⊑ι
checkpoint₉-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.reveal⊑-identity
        source-identity-reveal⊢
        source-identity-reveal-absent
        (CTI.conceal⊑-identity
          source-identity-conceal⊢
          source-identity-conceal-absent
          (CTI.cast⊑cast²
            source-shifted-id-result
            (symᶜ (id {μ = idᶜ} ★))
            (CTI.·⊑·²
              allocated-argument-imprecision
              stripped-data-imprecision)
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      I.ι⊑ι)

checkpoint₉-ladder : String
checkpoint₉-ladder = impLadderDefault checkpoint₉-imprecision

checkpoint₁₀-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₁₀ ⊑ less-checkpoint₁₀ ∶ I.ι⊑ι
checkpoint₁₀-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.reveal⊑-identity
        source-identity-reveal⊢
        source-identity-reveal-absent
        (CTI.conceal⊑-identity
          source-identity-conceal⊢
          source-identity-conceal-absent
          (CTI.cast⊑cast²
            source-shifted-id-result
            (symᶜ (id {μ = idᶜ} ★))
            (CTI.·⊑·²
              (CTI.ƛ⊑ƛ² {pA = I.★⊑★} {pB = I.★⊑★}
                (CTI.x⊑x² {p = I.★⊑★} Z Z))
              (CTI.⊑cast²
                (symᶜ (id {μ = idᶜ} ★))
                source-tagged-data-imprecision
                I.★⊑★))
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      I.ι⊑ι)

checkpoint₁₀-ladder : String
checkpoint₁₀-ladder = impLadderDefault checkpoint₁₀-imprecision

checkpoint₁₁-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₁₁ ⊑ less-checkpoint₁₁ ∶ I.ι⊑ι
checkpoint₁₁-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.reveal⊑-identity
        source-identity-reveal⊢
        source-identity-reveal-absent
        (CTI.conceal⊑-identity
          source-identity-conceal⊢
          source-identity-conceal-absent
          (CTI.cast⊑cast²
            source-shifted-id-result
            (symᶜ (id {μ = idᶜ} ★))
            source-tagged-data-imprecision
            I.★⊑★)
          I.★⊑★)
        I.★⊑★)
      I.ι⊑ι)

checkpoint₁₁-ladder : String
checkpoint₁₁-ladder = impLadderDefault checkpoint₁₁-imprecision

checkpoint₁₂-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₁₂ ⊑ less-checkpoint₁₂ ∶ I.ι⊑ι
checkpoint₁₂-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.reveal⊑-identity
        source-identity-reveal⊢
        source-identity-reveal-absent
        (CTI.conceal⊑-identity
          source-identity-conceal⊢
          source-identity-conceal-absent
          source-tagged-data-imprecision
          I.★⊑★)
        I.★⊑★)
      I.ι⊑ι)

checkpoint₁₂-ladder : String
checkpoint₁₂-ladder = impLadderDefault checkpoint₁₂-imprecision

checkpoint₁₃-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₁₃ ⊑ less-checkpoint₁₃ ∶ I.ι⊑ι
checkpoint₁₃-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      (CTI.reveal⊑-identity
        source-identity-reveal⊢
        source-identity-reveal-absent
        source-tagged-data-imprecision
        I.★⊑★)
      I.ι⊑ι)

checkpoint₁₃-ladder : String
checkpoint₁₃-ladder = impLadderDefault checkpoint₁₃-imprecision

checkpoint₁₄-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₁₄ ⊑ less-checkpoint₁₄ ∶ I.ι⊑ι
checkpoint₁₄-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.cast⊑cast²
      (applyConsistency (bind ℕᵗ) (symᶜ nat-consistent-star))
      (symᶜ nat-consistent-star)
      source-tagged-data-imprecision
      I.ι⊑ι)

checkpoint₁₄-ladder : String
checkpoint₁₄-ladder = impLadderDefault checkpoint₁₄-imprecision

checkpoint₁₅-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₁₅ ⊑ less-checkpoint₁₅ ∶ I.ι⊑ι
checkpoint₁₅-imprecision =
  CTI.·⊑·²
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² {p = I.ι⊑ι} Z Z))
    (CTI.κ⊑κ² (κℕ 42) I.ι⊑ι)

checkpoint₁₅-ladder : String
checkpoint₁₅-ladder = impLadderDefault checkpoint₁₅-imprecision

checkpoint₁₆-imprecision :
  source-only-world CTI.⊢²
    more-checkpoint₁₆ ⊑ less-checkpoint₁₆ ∶ I.ι⊑ι
checkpoint₁₆-imprecision = CTI.κ⊑κ² (κℕ 42) I.ι⊑ι

checkpoint₁₆-ladder : String
checkpoint₁₆-ladder = impLadderDefault checkpoint₁₆-imprecision


------------------------------------------------------------------------
-- Generated imprecision ladders
------------------------------------------------------------------------

checkpoint₀-ladder-pinned :
  checkpoint₀-ladder ≡
    "⟨⟩\n" ++
    "source term                  A                        ηᴸA                      ⊑ costs                                       ηᴿB                  B                    target term\n" ++
    "───────────────────────────  ───────────────────────  ───────────────────────  ────────────────────────────────────────────  ───────────────────  ───────────────────  ───────────────────────────\n" ++
    "□₁ · □₂                      ℕ                        ℕ                        ℕ⊑ℕ                                           ℕ                    ℕ                    □₁ · □₂\n" ++
    "├ λ♯0. □                     (ℕ ⇒ ℕ)                  (ℕ ⇒ ℕ)                  ℕ⊑ℕ, ℕ⊑ℕ                                      (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)              ├ λ♯0. □\n" ++
    "│ ♯0                         ℕ                        ℕ                        ℕ⊑ℕ                                           ℕ                    ℕ                    │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                  ℕ                        ℕ                        ℕ⊑ℕ                                           ℕ                    ℕ                    └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                    ★                        ★                        ★⊑★                                           ★                    ★                      □₁ · □₂\n" ++
    "  ├ □₁ · □₂                  (ℕ ⇒ ★)                  (ℕ ⇒ ★)                  ι⊑★, ★⊑★                                      (★ ⇒ ★)              (★ ⇒ ★)                ├ □₁ · □₂\n" ++
    "  │ ├ □ [ ℕ ]                ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))      ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))      ι⊑★, ★⊑★, ι⊑★, ★⊑★                            ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))    │ ├ ─\n" ++
    "  │ │ Λ□                     ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))  ∀ ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))  ∀⊑(mark X⊑★ at ♭0, ★⊑★, mark X⊑★ at ♭0, ★⊑★)  ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))    │ │ ─\n" ++
    "  │ │ λ♯0. □                 ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))    ((♭0 ⇒ ★) ⇒ (♭0 ⇒ ★))    mark X⊑★ at ♭0, ★⊑★, mark X⊑★ at ♭0, ★⊑★      ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))    │ │ λ♯0. □\n" ++
    "  │ │ ♯0                     (♭0 ⇒ ★)                 (♭0 ⇒ ★)                 mark X⊑★ at ♭0, ★⊑★                           (★ ⇒ ★)              (★ ⇒ ★)                │ │ ♯0\n" ++
    "  │ └ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)                  (ℕ ⇒ ★)                  ι⊑★, ★⊑★                                      (★ ⇒ ★)              (★ ⇒ ★)                │ └ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │   λ♯0. □                 (ℕ ⇒ ★)                  (ℕ ⇒ ★)                  ι⊑★, ★⊑★                                      (★ ⇒ ★)              (★ ⇒ ★)                │   λ♯0. □\n" ++
    "  │   □₁ · □₂                ★                        ★                        ★⊑★                                           ★                    ★                      │   □₁ · □₂\n" ++
    "  │   ├ λ♯1. □               (★ ⇒ ★)                  (★ ⇒ ★)                  ★⊑★, ★⊑★                                      (★ ⇒ ★)              (★ ⇒ ★)                │   ├ λ♯1. □\n" ++
    "  │   │ ♯1                   ★                        ★                        ★⊑★                                           ★                    ★                      │   │ ♯1\n" ++
    "  │   └ □ ⟨ ℕ↦★ ⟩            ★                        ★                        ★⊑★                                           ★                    ★                      │   └ □ ⟨ ★↦★ ⟩\n" ++
    "  │     ♯0                   ℕ                        ℕ                        ι⊑★                                           ★                    ★                      │     ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩                ℕ                        ℕ                        ι⊑★                                           ★                    ★                      └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                       ℕ                        ℕ                        ℕ⊑ℕ                                           ℕ                    ℕ                        42"
checkpoint₀-ladder-pinned = refl
checkpoint₁-ladder-pinned :
  checkpoint₁-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term                  A                    ηᴸA                  ⊑ costs                                 ηᴿB                  B                    target term\n" ++
    "───────────────────────────  ───────────────────  ───────────────────  ──────────────────────────────────────  ───────────────────  ───────────────────  ───────────────────────────\n" ++
    "□₁ · □₂                      ℕ                    ℕ                    ℕ⊑ℕ                                     ℕ                    ℕ                    □₁ · □₂\n" ++
    "├ λ♯0. □                     (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)              ℕ⊑ℕ, ℕ⊑ℕ                                (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)              ├ λ♯0. □\n" ++
    "│ ♯0                         ℕ                    ℕ                    ℕ⊑ℕ                                     ℕ                    ℕ                    │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                  ℕ                    ℕ                    ℕ⊑ℕ                                     ℕ                    ℕ                    └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                    ★                    ★                    ★⊑★                                     ★                    ★                      □₁ · □₂\n" ++
    "  ├ □₁ · □₂                  (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                (★ ⇒ ★)              (★ ⇒ ★)                ├ □₁ · □₂\n" ++
    "  │ ├ □ ↑ ⇒-rev              ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))  ((ℕ ⇒ ★) ⇒ (ℕ ⇒ ★))  ι⊑★, ★⊑★, ι⊑★, ★⊑★ + target unoccupied  ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))    │ ├ ─\n" ++
    "  │ │ λ♯0. □                 ((X ⇒ ★) ⇒ (X ⇒ ★))  ((X ⇒ ★) ⇒ (X ⇒ ★))  mark X⊑★ at X, ★⊑★, mark X⊑★ at X, ★⊑★  ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))    │ │ λ♯0. □\n" ++
    "  │ │ ♯0                     (X ⇒ ★)              (X ⇒ ★)              mark X⊑★ at X, ★⊑★                      (★ ⇒ ★)              (★ ⇒ ★)                │ │ ♯0\n" ++
    "  │ └ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                (★ ⇒ ★)              (★ ⇒ ★)                │ └ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │   λ♯0. □                 (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                (★ ⇒ ★)              (★ ⇒ ★)                │   λ♯0. □\n" ++
    "  │   □₁ · □₂                ★                    ★                    ★⊑★                                     ★                    ★                      │   □₁ · □₂\n" ++
    "  │   ├ λ♯1. □               (★ ⇒ ★)              (★ ⇒ ★)              ★⊑★, ★⊑★                                (★ ⇒ ★)              (★ ⇒ ★)                │   ├ λ♯1. □\n" ++
    "  │   │ ♯1                   ★                    ★                    ★⊑★                                     ★                    ★                      │   │ ♯1\n" ++
    "  │   └ □ ⟨ ℕ↦★ ⟩            ★                    ★                    ★⊑★                                     ★                    ★                      │   └ □ ⟨ ★↦★ ⟩\n" ++
    "  │     ♯0                   ℕ                    ℕ                    ι⊑★                                     ★                    ★                      │     ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩                ℕ                    ℕ                    ι⊑★                                     ★                    ★                      └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                       ℕ                    ℕ                    ℕ⊑ℕ                                     ℕ                    ℕ                        42"
checkpoint₁-ladder-pinned = refl
checkpoint₂-ladder-pinned :
  checkpoint₂-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term                  A                    ηᴸA                  ⊑ costs                                 ηᴿB                  B                    target term\n" ++
    "───────────────────────────  ───────────────────  ───────────────────  ──────────────────────────────────────  ───────────────────  ───────────────────  ───────────────────────────\n" ++
    "□₁ · □₂                      ℕ                    ℕ                    ℕ⊑ℕ                                     ℕ                    ℕ                    □₁ · □₂\n" ++
    "├ λ♯0. □                     (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)              ℕ⊑ℕ, ℕ⊑ℕ                                (ℕ ⇒ ℕ)              (ℕ ⇒ ℕ)              ├ λ♯0. □\n" ++
    "│ ♯0                         ℕ                    ℕ                    ℕ⊑ℕ                                     ℕ                    ℕ                    │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                  ℕ                    ℕ                    ℕ⊑ℕ                                     ℕ                    ℕ                    └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                    ★                    ★                    ★⊑★                                     ★                    ★                      □₁ · □₂\n" ++
    "  ├ □ ↑ ⇒-rev                (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★ + target unoccupied            (★ ⇒ ★)              (★ ⇒ ★)                ├ ─\n" ++
    "  │ □₁ · □₂                  (X ⇒ ★)              (X ⇒ ★)              mark X⊑★ at X, ★⊑★                      (★ ⇒ ★)              (★ ⇒ ★)                │ □₁ · □₂\n" ++
    "  │ ├ λ♯0. □                 ((X ⇒ ★) ⇒ (X ⇒ ★))  ((X ⇒ ★) ⇒ (X ⇒ ★))  mark X⊑★ at X, ★⊑★, mark X⊑★ at X, ★⊑★  ((★ ⇒ ★) ⇒ (★ ⇒ ★))  ((★ ⇒ ★) ⇒ (★ ⇒ ★))    │ ├ λ♯0. □\n" ++
    "  │ │ ♯0                     (X ⇒ ★)              (X ⇒ ★)              mark X⊑★ at X, ★⊑★                      (★ ⇒ ★)              (★ ⇒ ★)                │ │ ♯0\n" ++
    "  │ └ □ ↓ ⇒-con              (X ⇒ ★)              (X ⇒ ★)              mark X⊑★ at X, ★⊑★ + target unoccupied  (★ ⇒ ★)              (★ ⇒ ★)                │ └ ─\n" ++
    "  │   □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                (★ ⇒ ★)              (★ ⇒ ★)                │   □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │   λ♯0. □                 (ℕ ⇒ ★)              (ℕ ⇒ ★)              ι⊑★, ★⊑★                                (★ ⇒ ★)              (★ ⇒ ★)                │   λ♯0. □\n" ++
    "  │   □₁ · □₂                ★                    ★                    ★⊑★                                     ★                    ★                      │   □₁ · □₂\n" ++
    "  │   ├ λ♯1. □               (★ ⇒ ★)              (★ ⇒ ★)              ★⊑★, ★⊑★                                (★ ⇒ ★)              (★ ⇒ ★)                │   ├ λ♯1. □\n" ++
    "  │   │ ♯1                   ★                    ★                    ★⊑★                                     ★                    ★                      │   │ ♯1\n" ++
    "  │   └ □ ⟨ ℕ↦★ ⟩            ★                    ★                    ★⊑★                                     ★                    ★                      │   └ □ ⟨ ★↦★ ⟩\n" ++
    "  │     ♯0                   ℕ                    ℕ                    ι⊑★                                     ★                    ★                      │     ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩                ℕ                    ℕ                    ι⊑★                                     ★                    ★                      └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                       ℕ                    ℕ                    ℕ⊑ℕ                                     ℕ                    ℕ                        42"
checkpoint₂-ladder-pinned = refl
checkpoint₃-ladder-pinned :
  checkpoint₃-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                                 ηᴿB      B        target term\n" ++
    "─────────────────────────  ───────  ───────  ──────────────────────────────────────  ───────  ───────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                                     ★        ★          □₁ · □₂\n" ++
    "  ├ □ ↑ ⇒-rev              (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + target unoccupied            (★ ⇒ ★)  (★ ⇒ ★)    ├ ─\n" ++
    "  │ □ ↓ ⇒-con              (X ⇒ ★)  (X ⇒ ★)  mark X⊑★ at X, ★⊑★ + target unoccupied  (★ ⇒ ★)  (★ ⇒ ★)    │ ─\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                                (★ ⇒ ★)  (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                                (★ ⇒ ★)  (★ ⇒ ★)    │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                                     ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                                (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                                     ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                                     ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                                     ★        ★          │   ♯0\n" ++
    "  └ □ ⟨ ℕ↦ℕ ⟩              ℕ        ℕ        ι⊑★                                     ★        ★          └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                                     ℕ        ℕ            42"
checkpoint₃-ladder-pinned = refl
checkpoint₄-ladder-pinned :
  checkpoint₄-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                                 ηᴿB      B        target term\n" ++
    "─────────────────────────  ───────  ───────  ──────────────────────────────────────  ───────  ───────  ─────────────────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                                     ★        ★          □₁ · □₂\n" ++
    "  ├ □ ↑ ⇒-rev              (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★ + target unoccupied            (★ ⇒ ★)  (★ ⇒ ★)    ├ ─\n" ++
    "  │ □ ↓ ⇒-con              (X ⇒ ★)  (X ⇒ ★)  mark X⊑★ at X, ★⊑★ + target unoccupied  (★ ⇒ ★)  (★ ⇒ ★)    │ ─\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                                (★ ⇒ ★)  (★ ⇒ ★)    │ □ ⟨ (★ ⇒ ★)↦(★ ⇒ ★) ⟩\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                                (★ ⇒ ★)  (★ ⇒ ★)    │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                                     ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                                (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                                     ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                                     ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                                     ★        ★          │   ♯0\n" ++
    "  └ ─                      ℕ        ℕ        ι⊑★                                     ★        ★          └ □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                                     ℕ        ℕ            42"
checkpoint₄-ladder-pinned = refl
checkpoint₅-ladder-pinned :
  checkpoint₅-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                                 ηᴿB      B        target term\n" ++
    "─────────────────────────  ───────  ───────  ──────────────────────────────────────  ───────  ───────  ───────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ↑ id                   ★        ★        ★⊑★ + generator absent                  ★        ★          ─\n" ++
    "  ─                        ★        ★        ★⊑★                                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                                     ★        ★          □₁ · □₂\n" ++
    "  ├ □ ↓ ⇒-con              (X ⇒ ★)  (X ⇒ ★)  mark X⊑★ at X, ★⊑★ + target unoccupied  (★ ⇒ ★)  (★ ⇒ ★)    ├ ─\n" ++
    "  │ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                                (★ ⇒ ★)  (★ ⇒ ★)    │ ─\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                                (★ ⇒ ★)  (★ ⇒ ★)    │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                                     ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                                (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                                     ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                                     ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                                     ★        ★          │   ♯0\n" ++
    "  └ □ ↓ seal X             X        X        mark X⊑★ at X + target unoccupied       ★        ★          └ ─\n" ++
    "    ─                      ℕ        ℕ        ι⊑★                                     ★        ★            □ ⟨ ★↦★ ⟩\n" ++
    "    ─                      ℕ        ℕ        ι⊑★                                     ★        ★            □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                                     ℕ        ℕ            42"
checkpoint₅-ladder-pinned = refl
checkpoint₆-ladder-pinned :
  checkpoint₆-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                            ηᴿB      B        target term\n" ++
    "─────────────────────────  ───────  ───────  ─────────────────────────────────  ───────  ───────  ───────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                           (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ↑ id                   ★        ★        ★⊑★ + generator absent             ★        ★          ─\n" ++
    "  □ ↓ id                   ★        ★        ★⊑★ + generator absent             ★        ★          ─\n" ++
    "  ─                        ★        ★        ★⊑★                                ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                                ★        ★          □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)    ├ ─\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)    │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                                ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                           (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                                ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                                ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                                ★        ★          │   ♯0\n" ++
    "  └ □ ↑ unseal X           ℕ        ℕ        ι⊑★ + target unoccupied            ★        ★          └ ─\n" ++
    "    □ ↓ seal X             X        X        mark X⊑★ at X + target unoccupied  ★        ★            ─\n" ++
    "    ─                      ℕ        ℕ        ι⊑★                                ★        ★            □ ⟨ ★↦★ ⟩\n" ++
    "    ─                      ℕ        ℕ        ι⊑★                                ★        ★            □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                                ℕ        ℕ            42"
checkpoint₆-ladder-pinned = refl
checkpoint₇-ladder-pinned :
  checkpoint₇-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term                A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "─────────────────────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────────\n" ++
    "□₁ · □₂                    ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □                   (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0                       ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩                ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ↑ id                   ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ↓ id                   ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  ─                        ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂                  ★        ★        ★⊑★                     ★        ★          □₁ · □₂\n" ++
    "  ├ □ ⟨ (ℕ ⇒ ★)↦(ℕ ⇒ ★) ⟩  (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    ├ ─\n" ++
    "  │ λ♯0. □                 (ℕ ⇒ ★)  (ℕ ⇒ ★)  ι⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    │ λ♯0. □\n" ++
    "  │ □₁ · □₂                ★        ★        ★⊑★                     ★        ★          │ □₁ · □₂\n" ++
    "  │ ├ λ♯1. □               (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    │ ├ λ♯1. □\n" ++
    "  │ │ ♯1                   ★        ★        ★⊑★                     ★        ★          │ │ ♯1\n" ++
    "  │ └ □ ⟨ ℕ↦★ ⟩            ★        ★        ★⊑★                     ★        ★          │ └ □ ⟨ ★↦★ ⟩\n" ++
    "  │   ♯0                   ℕ        ℕ        ι⊑★                     ★        ★          │   ♯0\n" ++
    "  └ ─                      ℕ        ℕ        ι⊑★                     ★        ★          └ □ ⟨ ★↦★ ⟩\n" ++
    "    ─                      ℕ        ℕ        ι⊑★                     ★        ★            □ ⟨ ℕ↦★ ⟩\n" ++
    "    42                     ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ            42"
checkpoint₇-ladder-pinned = refl
checkpoint₈-ladder-pinned :
  checkpoint₈-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term      A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "───────────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────────\n" ++
    "□₁ · □₂          ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0             ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩      ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ↑ id         ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ↓ id         ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
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
checkpoint₈-ladder-pinned = refl
checkpoint₉-ladder-pinned :
  checkpoint₉-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term      A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "───────────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────────\n" ++
    "□₁ · □₂          ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □         (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0             ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩      ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ↑ id         ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ↓ id         ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
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
checkpoint₉-ladder-pinned = refl
checkpoint₁₀-ladder-pinned :
  checkpoint₁₀-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term    A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "─────────────  ───────  ───────  ──────────────────────  ───────  ───────  ─────────────\n" ++
    "□₁ · □₂        ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □       (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0           ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩    ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ↑ id       ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ↓ id       ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ⟨ ★↦★ ⟩    ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □₁ · □₂      ★        ★        ★⊑★                     ★        ★          □₁ · □₂\n" ++
    "  ├ λ♯0. □     (★ ⇒ ★)  (★ ⇒ ★)  ★⊑★, ★⊑★                (★ ⇒ ★)  (★ ⇒ ★)    ├ λ♯0. □\n" ++
    "  │ ♯0         ★        ★        ★⊑★                     ★        ★          │ ♯0\n" ++
    "  └ ─          ★        ★        ★⊑★                     ★        ★          └ □ ⟨ ★↦★ ⟩\n" ++
    "    □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★                     ★        ★            □ ⟨ ℕ↦★ ⟩\n" ++
    "    42         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ            42"
checkpoint₁₀-ladder-pinned = refl
checkpoint₁₁-ladder-pinned :
  checkpoint₁₁-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩  ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ↑ id     ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ↓ id     ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ⟨ ★↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ★↦★ ⟩\n" ++
    "  □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ          42"
checkpoint₁₁-ladder-pinned = refl
checkpoint₁₂-ladder-pinned :
  checkpoint₁₂-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩  ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ↑ id     ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ↓ id     ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ          42"
checkpoint₁₂-ladder-pinned = refl
checkpoint₁₃-ladder-pinned :
  checkpoint₁₃-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs                 ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ──────────────────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ                (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩  ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ↑ id     ★        ★        ★⊑★ + generator absent  ★        ★          ─\n" ++
    "  □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★                     ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42         ℕ        ℕ        ℕ⊑ℕ                     ℕ        ℕ          42"
checkpoint₁₃-ladder-pinned = refl
checkpoint₁₄-ladder-pinned :
  checkpoint₁₄-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs   ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        │ ♯0\n" ++
    "└ □ ⟨ ★↦ℕ ⟩  ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        └ □ ⟨ ★↦ℕ ⟩\n" ++
    "  □ ⟨ ℕ↦★ ⟩  ★        ★        ★⊑★       ★        ★          □ ⟨ ℕ↦★ ⟩\n" ++
    "  42         ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ          42"
checkpoint₁₄-ladder-pinned = refl
checkpoint₁₅-ladder-pinned :
  checkpoint₁₅-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term  A        ηᴸA      ⊑ costs   ηᴿB      B        target term\n" ++
    "───────────  ───────  ───────  ────────  ───────  ───────  ───────────\n" ++
    "□₁ · □₂      ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        □₁ · □₂\n" ++
    "├ λ♯0. □     (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ℕ⊑ℕ, ℕ⊑ℕ  (ℕ ⇒ ℕ)  (ℕ ⇒ ℕ)  ├ λ♯0. □\n" ++
    "│ ♯0         ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        │ ♯0\n" ++
    "└ 42         ℕ        ℕ        ℕ⊑ℕ       ℕ        ℕ        └ 42"
checkpoint₁₅-ladder-pinned = refl
checkpoint₁₆-ladder-pinned :
  checkpoint₁₆-ladder ≡
    "⟨X: X↦ℕ ⊑[X⊑★] ─⟩\n" ++
    "source term  A  ηᴸA  ⊑ costs  ηᴿB  B  target term\n" ++
    "───────────  ─  ───  ───────  ───  ─  ───────────\n" ++
    "42           ℕ  ℕ    ℕ⊑ℕ      ℕ    ℕ  42"
checkpoint₁₆-ladder-pinned = refl
