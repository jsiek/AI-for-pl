{-# OPTIONS --safe #-}

module proof.DGG.notes.CTIBalancePrimitiveProbe where

-- File Charter:
--   * Checks a source-typed primitive wrapper around the smallest existing
--     target-rebase driver that returns data on both sides.
--   * Proves source typing, gradual imprecision, exact ordinary compilation,
--     evaluation to 43, and the live-frame primitive checkpoint shape.
--   * Does not change CTI and is not part of the trusted Examples catalog.

open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TermCtx using (Z)
open import Consistency
open import GradualTerms renaming (_∣_⊢_⦂_ to _∣_⊢ᴳ_⦂_)
import GradualTermImprecision as GTI
import Imprecision as I
open import TyStore using (store-empty)
open import CastTerms using (Ctx; Term; ⟨_,_,_⟩; Δᵉ; _⊢_⦂_)
import CastTerms as C
open import Compile using (compile)
open import Primitives using (addℕ; κℕ)
import Example as Ex
import proof.DGG.CastTermImprecision as CTI
import proof.DGG.Examples.TargetIdentityConceal as TIC
import proof.DGG.Examples.TargetIdentityReveal as TReveal
open import proof.DGG.World using (_⊑ᶜ_; _⊑ᵀ⟨_⟩_)

open GTI using () renaming
  (_∣_⊢ᴳ_⊑_⦂_⊑_∶_ to _∣_⊢ᴳ²_⊑_⦂_⊑_∶_)


------------------------------------------------------------------------
-- Source pair
------------------------------------------------------------------------

ℓ-add : Label
ℓ-add = 5

more-precise : GTerm 0
more-precise =
  (((((ƛ TIC.∀higher-X ⇒ ` 0) ·[ TIC.ℓ-cast ]
    (Λ (ƛ TIC.X⇒★ ⇒ ` 0))) `[ TIC.ℕᵗ ]) ·[ TIC.ℓ-higher ]
    (ƛ TIC.ℕᵗ ⇒ ((ƛ ★ ⇒ ` 0) ·[ TIC.ℓ-inner ] ` 0)))
    ·[ TIC.ℓ-data ] $ (κℕ 42))
  ⊕[ addℕ at ℓ-add ] $ (κℕ 1)

less-precise : GTerm 0
less-precise =
  ((((ƛ TIC.higher-dynamic ⇒ ` 0) ·[ TIC.ℓ-cast ]
    (Λ (ƛ TIC.X⇒★ ⇒ ` 0))) ·[ TIC.ℓ-higher ]
    (ƛ ★ ⇒ ((ƛ ★ ⇒ ` 0) ·[ TIC.ℓ-inner ] ` 0)))
    ·[ TIC.ℓ-data ] $ (κℕ 42))
  ⊕[ addℕ at ℓ-add ] $ (κℕ 1)


------------------------------------------------------------------------
-- Source typing and gradual imprecision
------------------------------------------------------------------------

more-precise-⊢ : 0 ∣ [] ⊢ᴳ more-precise ⦂ TIC.ℕᵗ
more-precise-⊢ =
  ⊢⊕ addℕ TIC.more-core-⊢ TIC.star-consistent-nat
    (⊢$ (κℕ 1)) (id (‵ `ℕ))

less-precise-⊢ : 0 ∣ [] ⊢ᴳ less-precise ⦂ TIC.ℕᵗ
less-precise-⊢ =
  ⊢⊕ addℕ TIC.less-core-⊢ TIC.star-consistent-nat
    (⊢$ (κℕ 1)) (id (‵ `ℕ))

source-imprecision :
  I.idᵐ ∣ [] ⊢ᴳ² more-precise ⊑ less-precise
    ⦂ TIC.ℕᵗ ⊑ TIC.ℕᵗ ∶ I.ι⊑ι
source-imprecision =
  GTI.⊕⊑⊕ᴳ addℕ TIC.core-imprecision
    TIC.star-consistent-nat TIC.star-consistent-nat
    (GTI.κ⊑κᴳ (κℕ 1)) (id (‵ `ℕ)) (id (‵ `ℕ))


------------------------------------------------------------------------
-- Exact ordinary compilation and data result
------------------------------------------------------------------------

more-compiled : Term 0
more-compiled = proj₁ (compile {Σ = store-empty} more-precise-⊢)

more-compiled-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ more-compiled ⦂ TIC.ℕᵗ
more-compiled-⊢ = proj₂ (compile {Σ = store-empty} more-precise-⊢)

less-compiled : Term 0
less-compiled = proj₁ (compile {Σ = store-empty} less-precise-⊢)

less-compiled-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ less-compiled ⦂ TIC.ℕᵗ
less-compiled-⊢ = proj₂ (compile {Σ = store-empty} less-precise-⊢)

more-compiled-shape :
  more-compiled ≡
    ((proj₁ (compile {Σ = store-empty} TIC.more-core-⊢)
      C.⟨ TIC.star-consistent-nat ⟩) C.⊕[ addℕ ]
      (C.$ (κℕ 1) C.⟨ id (‵ `ℕ) ⟩))
more-compiled-shape = refl

less-compiled-shape :
  less-compiled ≡
    ((proj₁ (compile {Σ = store-empty} TIC.less-core-⊢)
      C.⟨ TIC.star-consistent-nat ⟩) C.⊕[ addℕ ]
      (C.$ (κℕ 1) C.⟨ id (‵ `ℕ) ⟩))
less-compiled-shape = refl

more-evaluates-to-43 :
  Ex.evalNat Ex.gas more-compiled-⊢ ≡ just 43
more-evaluates-to-43 = refl

less-evaluates-to-43 :
  Ex.evalNat Ex.gas less-compiled-⊢ ≡ just 43
less-evaluates-to-43 = refl


------------------------------------------------------------------------
-- Extract and reuse the trusted live-frame checkpoint
------------------------------------------------------------------------

source-application-argument : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {L L′ M M′ A B} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → γ CTI.⊢² L C.· M ⊑ L′ C.· M′ ∶ p
  → Term (Δᵉ Γᴸ)
source-application-argument {M = M} related = M

target-application-argument : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {L L′ M M′ A B} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → γ CTI.⊢² L C.· M ⊑ L′ C.· M′ ∶ p
  → Term (Δᵉ Γᴿ)
target-application-argument {M′ = M′} related = M′

lift-identity-argument-through-primitive : ∀ {Γᴸ Γᴿ : Ctx}
    {γ : Γᴸ ⊑ᶜ Γᴿ} {M M′}
  → (related : γ CTI.⊢²
      (C.ƛ (C.` 0)) C.· M ⊑ (C.ƛ (C.` 0)) C.· M′
        ∶ I.ι⊑ι {ι = `ℕ})
  → γ CTI.⊢²
      M C.⊕[ addℕ ]
        (C.$ (κℕ 1) C.⟨ id {μ = idᶜ {Δ = Δᵉ Γᴸ}} (‵ `ℕ) ⟩)
      ⊑ M′ C.⊕[ addℕ ]
        (C.$ (κℕ 1) C.⟨ id {μ = idᶜ {Δ = Δᵉ Γᴿ}} (‵ `ℕ) ⟩)
        ∶ I.ι⊑ι {ι = `ℕ}
lift-identity-argument-through-primitive {Γᴸ = Γᴸ} {Γᴿ = Γᴿ}
    (CTI.·⊑·²
      (CTI.ƛ⊑ƛ² (CTI.x⊑x² Z Z)) argument-related) =
  CTI.⊕⊑⊕² addℕ argument-related
    (CTI.cast⊑cast²
      (id {μ = idᶜ {Δ = Δᵉ Γᴸ}} (‵ `ℕ))
      (id {μ = idᶜ {Δ = Δᵉ Γᴿ}} (‵ `ℕ))
      (CTI.κ⊑κ² (κℕ 1) (I.ι⊑ι {ι = `ℕ}))
      (I.ι⊑ι {ι = `ℕ}))
    (I.ι⊑ι {ι = `ℕ})

primitive-checkpoint-imprecision :
  TReveal.checkpoint₃-beta-current CTI.⊢²
    source-application-argument TIC.checkpoint₁₀-imprecision
      C.⊕[ addℕ ] (C.$ (κℕ 1) C.⟨ id (‵ `ℕ) ⟩)
    ⊑ target-application-argument TIC.checkpoint₁₀-imprecision
      C.⊕[ addℕ ] (C.$ (κℕ 1) C.⟨ id (‵ `ℕ) ⟩)
    ∶ I.ι⊑ι {ι = `ℕ}
primitive-checkpoint-imprecision =
  lift-identity-argument-through-primitive
    TIC.checkpoint₁₀-imprecision
