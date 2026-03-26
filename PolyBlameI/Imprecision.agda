module Imprecision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; subst)

open import Types
open import TypeSubst

------------------------------------------------------------------------
-- Intrinsic imprecision
--
--   p ::= g | id_⋆ | g;tag_G | seal_α;p | να.p[α]
------------------------------------------------------------------------

infixr 7 _→ᵖ_
infixl 8 _；tag_
infixr 8 seal_；_
infix 4 _∣_∣_⊢_⊑_
infix 4 _∣_∣_⊢ᶜ_⊑_

mutual
  data _∣_∣_⊢ᶜ_⊑_ (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store Ψ)
       : Ty Δ Ψ → Ty Δ Ψ → Set where
    idα  : ∀ (α : Seal Ψ) →
           Δ ∣ Ψ ∣ Σ ⊢ᶜ (｀ α) ⊑ (｀ α)

    idX  : (X : TyVar Δ) →
           Δ ∣ Ψ ∣ Σ ⊢ᶜ (＇ X) ⊑ (＇ X)

    idι  : (ι : Base) →
           Δ ∣ Ψ ∣ Σ ⊢ᶜ (‵ ι) ⊑ (‵ ι)

    _→ᵖ_ : {A A′ B B′ : Ty Δ Ψ} →
           Δ ∣ Ψ ∣ Σ ⊢ A ⊑ A′ →
           Δ ∣ Ψ ∣ Σ ⊢ B ⊑ B′ →
           Δ ∣ Ψ ∣ Σ ⊢ᶜ (A ⇒ B) ⊑ (A′ ⇒ B′)

    ∀ᵖ_  : {A B : Ty (suc Δ) Ψ} →
           (suc Δ) ∣ Ψ ∣ Σ ⊢ A ⊑ B →
           Δ ∣ Ψ ∣ Σ ⊢ᶜ (`∀ A) ⊑ (`∀ B)

  data _∣_∣_⊢_⊑_ (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store Ψ)
       : Ty Δ Ψ → Ty Δ Ψ → Set where
    ⌈_⌉ : {A B : Ty Δ Ψ} →
          Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ B →
          Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B

    id⋆ : Δ ∣ Ψ ∣ Σ ⊢ `★ ⊑ `★

    tag_∘_ : {A G : Ty Δ Ψ} (g : Ground G)
             → Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ G
             → Δ ∣ Ψ ∣ Σ ⊢ A ⊑ `★

    seal_；_ : {α : Seal Ψ} {A : Ty 0 Ψ} {B : Ty Δ Ψ} →
               Σ ∋ˢ α ⦂ A →
               Δ ∣ Ψ ∣ Σ ⊢ (wkTy0 A) ⊑ B →
               Δ ∣ Ψ ∣ Σ ⊢ (｀ α) ⊑ B

    ν_ : {A : Ty (suc Δ) Ψ} {B : Ty Δ Ψ} →
         Δ ∣ (suc Ψ) ∣ ((Zˢ , `★) ∷ ⟰ˢ Σ) ⊢ (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ⊑ (⇑ˢ B) →
         Δ ∣ Ψ ∣ Σ ⊢ (`∀ A) ⊑ B

pattern _；tag_ p g = tag g ∘ p

------------------------------------------------------------------------
-- Renaming/substitution for imprecision witnesses
------------------------------------------------------------------------

mutual
  idⱽ : ∀{Δ}{Ψ}{Σ : Store Ψ} (A : TVar Δ Ψ) →
        Δ ∣ Ψ ∣ Σ ⊢ᶜ tvTy A ⊑ tvTy A
  idⱽ (＇ X) = idX X
  idⱽ (｀ α) = idα α

cong-⊑-≡ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{A A′ B B′ : Ty Δ Ψ} →
  A ≡ A′ →
  B ≡ B′ →
  Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
  Δ ∣ Ψ ∣ Σ ⊢ A′ ⊑ B′
cong-⊑-≡ refl refl p = p

castΣ⊑ :
  ∀ {Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ≡ Σ′ →
  Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
  Δ ∣ Ψ ∣ Σ′ ⊢ A ⊑ B
castΣ⊑ refl p = p

mutual
  renameᵗᶜ :
    ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameᵗ Δ Δ′) →
    Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ B →
    Δ′ ∣ Ψ ∣ Σ ⊢ᶜ renameᵗ ρ A ⊑ renameᵗ ρ B
  renameᵗᶜ ρ (idα α) = idα α
  renameᵗᶜ ρ (idX X) = idX (ρ X)
  renameᵗᶜ ρ (idι ι) = idι ι
  renameᵗᶜ ρ (p →ᵖ q) = renameᵗᵖ ρ p →ᵖ renameᵗᵖ ρ q
  renameᵗᶜ ρ (∀ᵖ p) = ∀ᵖ (renameᵗᵖ (extᵗ ρ) p)

  renameᵗᵖ :
    ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameᵗ Δ Δ′) →
    Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
    Δ′ ∣ Ψ ∣ Σ ⊢ renameᵗ ρ A ⊑ renameᵗ ρ B
  renameᵗᵖ ρ ⌈ g ⌉ = ⌈ renameᵗᶜ ρ g ⌉
  renameᵗᵖ ρ id⋆ = id⋆
  renameᵗᵖ {Δ′ = Δ′} {Ψ = Ψ} {Σ = Σ} {A = A} ρ (p ；tag g) =
    (renameᵗᶜ ρ p) ；tag (renameᵗ-ground ρ g)
  renameᵗᵖ {Δ′ = Δ′} {Ψ = Ψ} {Σ = Σ} {B = B} ρ (seal_；_ {A = A} h p) =
    seal h ；
      subst
        (λ T → Δ′ ∣ Ψ ∣ Σ ⊢ T ⊑ renameᵗ ρ B)
        (renameᵗ-wkTy0 ρ A)
        (renameᵗᵖ ρ p)
  renameᵗᵖ ρ (ν_ {A = A} {B = B} p) =
    ν (cong-⊑-≡ (renameᵗ-ν-src ρ A) (renameᵗ-⇑ˢ ρ B) (renameᵗᵖ ρ p))

mutual
  substᵗᶜ :
    ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (σ : Substᵗ Δ Δ′ Ψ) →
    Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ B →
    Δ′ ∣ Ψ ∣ Σ ⊢ᶜ substᵗ σ A ⊑ substᵗ σ B
  substᵗᶜ σ (idα α) = idα α
  substᵗᶜ σ (idX X) = idⱽ (σ X)
  substᵗᶜ σ (idι ι) = idι ι
  substᵗᶜ σ (p →ᵖ q) = substᵗᵖ σ p →ᵖ substᵗᵖ σ q
  substᵗᶜ σ (∀ᵖ p) = ∀ᵖ (substᵗᵖ (extsᵗ σ) p)

  substᵗᵖ :
    ∀ {Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (σ : Substᵗ Δ Δ′ Ψ) →
    Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
    Δ′ ∣ Ψ ∣ Σ ⊢ substᵗ σ A ⊑ substᵗ σ B
  substᵗᵖ σ ⌈ g ⌉ = ⌈ substᵗᶜ σ g ⌉
  substᵗᵖ σ id⋆ = id⋆
  substᵗᵖ {Δ′ = Δ′} {Ψ = Ψ} {Σ = Σ} {A = A} σ (p ；tag G) =
    (substᵗᶜ σ p) ；tag substᵗ-ground σ G
  substᵗᵖ {Δ′ = Δ′} {Ψ = Ψ} {Σ = Σ} {B = B} σ (seal_；_ {A = A} h p) =
    seal h ；
      subst
        (λ T → Δ′ ∣ Ψ ∣ Σ ⊢ T ⊑ substᵗ σ B)
        (substᵗ-wkTy0 σ A)
        (substᵗᵖ σ p)
  substᵗᵖ σ (ν_ {A = A} {B = B} p) =
    ν (cong-⊑-≡ (substᵗ-ν-src σ A) (substᵗ-⇑ˢ σ B) (substᵗᵖ (liftSubstˢ σ) p))

mutual
  renameˢᶜ :
    ∀ {Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameˢ Ψ Ψ′) →
    Δ ∣ Ψ ∣ Σ ⊢ᶜ A ⊑ B →
    Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ⊢ᶜ renameˢ ρ A ⊑ renameˢ ρ B
  renameˢᶜ ρ (idα α) = idα (ρ α)
  renameˢᶜ ρ (idX X) = idX X
  renameˢᶜ ρ (idι ι) = idι ι
  renameˢᶜ ρ (p →ᵖ q) = renameˢᵖ ρ p →ᵖ renameˢᵖ ρ q
  renameˢᶜ ρ (∀ᵖ p) = ∀ᵖ (renameˢᵖ ρ p)

  renameˢᵖ :
    ∀ {Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameˢ Ψ Ψ′) →
    Δ ∣ Ψ ∣ Σ ⊢ A ⊑ B →
    Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ⊢ renameˢ ρ A ⊑ renameˢ ρ B
  renameˢᵖ ρ ⌈ g ⌉ = ⌈ renameˢᶜ ρ g ⌉
  renameˢᵖ ρ id⋆ = id⋆
  renameˢᵖ {Δ = Δ} {Ψ′ = Ψ′} {Σ = Σ} {A = A} ρ (p ；tag g) =
    (renameˢᶜ ρ p) ；tag (renameˢ-ground ρ g)
  renameˢᵖ {Δ = Δ} {Ψ′ = Ψ′} {Σ = Σ} {B = B} ρ (seal_；_ {A = A} h p) =
    seal (renameLookupˢ ρ h) ；
      subst
        (λ T → Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ⊢ T ⊑ renameˢ ρ B)
        (renameˢ-wkTy0 {Δ = Δ} ρ A)
        (renameˢᵖ ρ p)
  renameˢᵖ {Σ = Σ} ρ (ν_ {A = A} {B = B} p) =
    ν (cong-⊑-≡
         (renameˢ-ν-src ρ A)
         (renameˢ-⇑ˢ ρ B)
         (castΣ⊑ (renameStoreˢ-↑★ ρ Σ) (renameˢᵖ (extˢ ρ) p)))
