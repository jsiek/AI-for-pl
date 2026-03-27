module Coercions where

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans) renaming (subst to substEq)
open import Types
open import TypeSubst

------------------------------------------------------------------------
-- Instantiate top type variable with ★ (needed for ℐ : ∀X.A ⇒ A[X := ★])
------------------------------------------------------------------------

single★ : ∀{Δ}{Ψ} → Substᵗ (suc Δ) Δ Ψ
single★ Zᵗ = `★
single★ (Sᵗ X) = ＇ X

inst★ : ∀{Δ}{Ψ} → Ty (suc Δ) Ψ → Ty Δ Ψ
inst★ A = substᵗ single★ A

inst★-renameᵗ-suc :
  ∀{Δ}{Ψ} (A : Ty Δ Ψ) →
  inst★ (renameᵗ Sᵗ A) ≡ A
inst★-renameᵗ-suc A =
  trans
    (substᵗ-renameᵗ Sᵗ single★ A)
    (trans
      (substᵗ-cong (λ X → refl) A)
      (substᵗ-id A))

renameᵗ-inst★ :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (A : Ty (suc Δ) Ψ) →
  renameᵗ ρ (inst★ A) ≡ inst★ (renameᵗ (extᵗ ρ) A)
renameᵗ-inst★ {Ψ = Ψ} ρ A =
  trans
    (renameᵗ-substᵗ ρ single★ A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-renameᵗ (extᵗ ρ) single★ A)))
  where
    env :
      (X : TyVar (suc _)) →
      renameᵗ ρ (single★ {Ψ = Ψ} X) ≡ single★ {Ψ = Ψ} (extᵗ ρ X)
    env Zᵗ = refl
    env (Sᵗ X) = refl

substᵗ-inst★ :
  ∀{Δ}{Δ′}{Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (A : Ty (suc Δ) Ψ) →
  substᵗ σ (inst★ A) ≡ inst★ (substᵗ (extsᵗ σ) A)
substᵗ-inst★ σ A =
  trans
    (substᵗ-substᵗ σ single★ A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-substᵗ single★ (extsᵗ σ) A)))
  where
    env :
      (X : TyVar (suc _)) →
      substᵗ σ (single★ X) ≡ substᵗ single★ (extsᵗ σ X)
    env Zᵗ = refl
    env (Sᵗ X) = sym (inst★-renameᵗ-suc (σ X))

renameˢ-inst★ :
  ∀{Δ}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (A : Ty (suc Δ) Ψ) →
  renameˢ ρ (inst★ A) ≡ inst★ (renameˢ ρ A)
renameˢ-inst★ ρ A =
  trans
    (renameˢ-substᵗ ρ single★ A)
    (substᵗ-cong env (renameˢ ρ A))
  where
    env :
      (X : TyVar (suc _)) →
      renameˢ ρ (single★ X) ≡ single★ X
    env Zᵗ = refl
    env (Sᵗ X) = refl

------------------------------------------------------------------------
-- Intrinsically typed coercions
------------------------------------------------------------------------

infixr 7 _↦_
infixr 6 _⨟_

data Coercion {Δ}{Ψ} (Σ : Store Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
  id : ∀{A}
     → Coercion Σ A A

  _`?_ : ∀{G}
       → Ground G
       → Coercion Σ `★ G

  _! : ∀{G}
     → Ground G
     → Coercion Σ G `★

  _⁻ : ∀{α}{A}
     → Σ ∋ˢ α ⦂ A
     → Coercion Σ (wkTy0 A) (｀ α)

  _⁺ : ∀{α}{A}
     → Σ ∋ˢ α ⦂ A
     → Coercion Σ (｀ α) (wkTy0 A)

  _↦_ : ∀{A A′ B B′}
      → Coercion Σ A′ A
      → Coercion Σ B B′
      → Coercion Σ (A ⇒ B) (A′ ⇒ B′)

  _⨟_ : ∀{A B C}
      → Coercion Σ A B
      → Coercion Σ B C
      → Coercion Σ A C

  ∀ᶜ_ : ∀{A B}
      → Coercion {Δ = suc Δ} Σ A B
      → Coercion {Δ = Δ} Σ (`∀ A) (`∀ B)

  𝒢 : ∀{A}
    → Coercion Σ A (`∀ (renameᵗ Sᵗ A))

  ℐ : ∀{A}
    → Coercion Σ (`∀ A) (inst★ A)

------------------------------------------------------------------------
-- Type-variable renaming and substitution for coercions
------------------------------------------------------------------------

renameᶜᵗ :
  ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B}
  (ρ : Renameᵗ Δ Δ′) →
  Coercion {Δ}{Ψ} Σ A B →
  Coercion {Δ′}{Ψ} Σ (renameᵗ ρ A) (renameᵗ ρ B)
renameᶜᵗ ρ id = id
renameᶜᵗ ρ ((_`?_) g) = (_`?_) (renameᵗ-ground ρ g)
renameᶜᵗ ρ (g !) = renameᵗ-ground ρ g !
renameᶜᵗ ρ (_⁻ {A = A₀} h) rewrite renameᵗ-wkTy0 ρ A₀ = h ⁻
renameᶜᵗ ρ (_⁺ {A = A₀} h) rewrite renameᵗ-wkTy0 ρ A₀ = h ⁺
renameᶜᵗ ρ (c ↦ d) = renameᶜᵗ ρ c ↦ renameᶜᵗ ρ d
renameᶜᵗ ρ (c ⨟ d) = renameᶜᵗ ρ c ⨟ renameᶜᵗ ρ d
renameᶜᵗ ρ (∀ᶜ c) = ∀ᶜ (renameᶜᵗ (extᵗ ρ) c)
renameᶜᵗ ρ (𝒢 {A = A}) =
  substEq
    (λ T → Coercion _ (renameᵗ ρ A) (`∀ T))
    (renameᵗ-suc-comm ρ A)
    𝒢
renameᶜᵗ ρ (ℐ {A = A}) =
  substEq
    (λ T → Coercion _ (`∀ (renameᵗ (extᵗ ρ) A)) T)
    (sym (renameᵗ-inst★ ρ A))
    ℐ

substᶜᵗ :
  ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B}
  (σ : Substᵗ Δ Δ′ Ψ) →
  Coercion {Δ}{Ψ} Σ A B →
  Coercion {Δ′}{Ψ} Σ (substᵗ σ A) (substᵗ σ B)
substᶜᵗ σ id = id
substᶜᵗ σ ((_`?_) g) = (_`?_) (substᵗ-ground σ g)
substᶜᵗ σ (g !) = substᵗ-ground σ g !
substᶜᵗ σ (_⁻ {A = A₀} h) rewrite substᵗ-wkTy0 σ A₀ = h ⁻
substᶜᵗ σ (_⁺ {A = A₀} h) rewrite substᵗ-wkTy0 σ A₀ = h ⁺
substᶜᵗ σ (c ↦ d) = substᶜᵗ σ c ↦ substᶜᵗ σ d
substᶜᵗ σ (c ⨟ d) = substᶜᵗ σ c ⨟ substᶜᵗ σ d
substᶜᵗ σ (∀ᶜ c) = ∀ᶜ (substᶜᵗ (extsᵗ σ) c)
substᶜᵗ σ (𝒢 {A = A}) =
  substEq
    (λ T → Coercion _ (substᵗ σ A) (`∀ T))
    (sym (substᵗ-suc-renameᵗ-suc σ A))
    𝒢
substᶜᵗ σ (ℐ {A = A}) =
  substEq
    (λ T → Coercion _ (`∀ (substᵗ (extsᵗ σ) A)) T)
    (sym (substᵗ-inst★ σ A))
    ℐ

------------------------------------------------------------------------
-- Seal renaming for coercions
------------------------------------------------------------------------

renameᶜˢ :
  ∀{Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B}
  (ρ : Renameˢ Ψ Ψ′) →
  Coercion {Δ}{Ψ} Σ A B →
  Coercion {Δ}{Ψ′} (renameStoreˢ ρ Σ) (renameˢ ρ A) (renameˢ ρ B)
renameᶜˢ ρ id = id
renameᶜˢ ρ ((_`?_) g) = (_`?_) (renameˢ-ground ρ g)
renameᶜˢ ρ (g !) = renameˢ-ground ρ g !
renameᶜˢ {Δ = Δ} ρ (_⁻ {A = A₀} h)
  rewrite renameˢ-wkTy0 {Δ = Δ} ρ A₀ =
  (renameLookupˢ ρ h) ⁻
renameᶜˢ {Δ = Δ} ρ (_⁺ {A = A₀} h)
  rewrite renameˢ-wkTy0 {Δ = Δ} ρ A₀ =
  (renameLookupˢ ρ h) ⁺
renameᶜˢ ρ (c ↦ d) = renameᶜˢ ρ c ↦ renameᶜˢ ρ d
renameᶜˢ ρ (c ⨟ d) = renameᶜˢ ρ c ⨟ renameᶜˢ ρ d
renameᶜˢ ρ (∀ᶜ c) = ∀ᶜ (renameᶜˢ ρ c)
renameᶜˢ ρ (𝒢 {A = A}) =
  substEq
    (λ T → Coercion _ (renameˢ ρ A) (`∀ T))
    (renameᵗ-renameˢ Sᵗ ρ A)
    𝒢
renameᶜˢ ρ (ℐ {A = A}) =
  substEq
    (λ T → Coercion _ (`∀ (renameˢ ρ A)) T)
    (sym (renameˢ-inst★ ρ A))
    ℐ
