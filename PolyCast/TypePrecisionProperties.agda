module TypePrecisionProperties where

-- File Charter:
--   * Structural metatheory for the type-precision judgments from `TypePrecision`.
--   * Weakening, renaming, substitution, and seal-opening transport lemmas for `⊑`.
--   * Small helper lemmas may live here when they exist only to support precision transport.
-- Note to self:
--   * Keep the definition of precision itself in `TypePrecision.agda`; this file is for
--     its reusable properties.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality as Eq using (sym; trans; cong; cong₂)

open import Types
open import Store
  using
    ( _⊆ˢ_
    ; ⊆ˢ-refl
    ; drop
    ; wkLookupˢ
    ; ν-⊆ˢ
    )
open import PolyCast using (substᵗ-[]ᵗ-seal)
open import TypePrecision
open import TypeSubst
  using
    ( renameLookupˢ
    ; renameˢ-ground
    ; renameˢ-substᵗ
    ; renameˢ-ext-⇑ˢ
    ; renameˢ-[]ᵗ-seal
    ; renameˢ-wkTy0
    ; substᵗ-cong
    ; substᵗ-ground
    ; substᵗ-wkTy0
    ; substᵗ-⇑ˢ
    ; renameᵗ-⇑ˢ
    ; liftSubstˢ
    ; exts-liftSubstˢ
    )

renameStoreˢ-ext-⟰ˢ :
  ∀{Ψ}{Ψ′} →
  (ρ : Renameˢ Ψ Ψ′) →
  (Σ : Store Ψ) →
  renameStoreˢ (extˢ ρ) (⟰ˢ Σ) ≡ ⟰ˢ (renameStoreˢ ρ Σ)
renameStoreˢ-ext-⟰ˢ ρ [] = refl
renameStoreˢ-ext-⟰ˢ ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-ext-⇑ˢ ρ A))
    (renameStoreˢ-ext-⟰ˢ ρ Σ)

renameStoreˢ-ext-ν :
  ∀{Ψ}{Ψ′} →
  (ρ : Renameˢ Ψ Ψ′) →
  (Σ : Store Ψ) →
  renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ≡
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ (renameStoreˢ ρ Σ))
renameStoreˢ-ext-ν ρ Σ =
  cong₂ _∷_
    (cong₂ _,_ refl refl)
    (renameStoreˢ-ext-⟰ˢ ρ Σ)

mutual
  ⊑ᵃ-wkΣ :
    ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
    Σ ⊆ˢ Σ′ →
    Σ ⊢ A ⊑ᵃ B →
    Σ′ ⊢ A ⊑ᵃ B
  ⊑ᵃ-wkΣ w (tag g) = tag g
  ⊑ᵃ-wkΣ w (seal h) = seal (wkLookupˢ w h)
  ⊑ᵃ-wkΣ w (_↦_ {A = A} {A′ = A′} {B = B} {B′ = B′} p q) =
    _↦_ {A = A} {A′ = A′} {B = B} {B′ = B′}
      (⊑-wkΣ w p)
      (⊑-wkΣ w q)
  ⊑ᵃ-wkΣ w (∀ᵖ p) = ∀ᵖ (⊑-wkΣ w p)
  ⊑ᵃ-wkΣ w (ν c) = ν (⊑-wkΣ (ν-⊆ˢ `★ w) c)

  ⊑-wkΣ :
    ∀{Δ}{Ψ}{Σ Σ′ : Store Ψ}{A B : Ty Δ Ψ} →
    Σ ⊆ˢ Σ′ →
    Σ ⊢ A ⊑ B →
    Σ′ ⊢ A ⊑ B
  ⊑-wkΣ w id = id
  ⊑-wkΣ w (p ； a) = (⊑-wkΣ w p) ； (⊑ᵃ-wkΣ w a)

mutual
  ⊑ᵃ-renameˢ :
    ∀{Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameˢ Ψ Ψ′) →
    Σ ⊢ A ⊑ᵃ B →
    renameStoreˢ ρ Σ ⊢ renameˢ ρ A ⊑ᵃ renameˢ ρ B
  ⊑ᵃ-renameˢ ρ (tag g) = tag (renameˢ-ground ρ g)
  ⊑ᵃ-renameˢ ρ (seal {α = α} {A = A} h) =
    Eq.subst
      (λ T → _ ⊢ T ⊑ᵃ ｀ (ρ α))
      (Eq.sym (renameˢ-wkTy0 ρ A))
      (seal (renameLookupˢ ρ h))
  ⊑ᵃ-renameˢ ρ (_↦_ {A = A} {A′ = A′} {B = B} {B′ = B′} p q) =
    _↦_ {A = renameˢ ρ A}
        {A′ = renameˢ ρ A′}
        {B = renameˢ ρ B}
        {B′ = renameˢ ρ B′}
      (⊑-renameˢ ρ p)
      (⊑-renameˢ ρ q)
  ⊑ᵃ-renameˢ ρ (∀ᵖ p) = ∀ᵖ (⊑-renameˢ ρ p)
  ⊑ᵃ-renameˢ {Σ = Σ} {A = `∀ A} {B = B} ρ (ν c) =
    ν
      (Eq.subst
        (λ Σ′ →
          Σ′ ⊢
            ((⇑ˢ (renameˢ ρ A)) [ ｀ Zˢ ]ᵗ) ⊑
            (⇑ˢ (renameˢ ρ B)))
        (renameStoreˢ-ext-ν ρ Σ)
        (Eq.subst
          (λ T →
            renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
              ((⇑ˢ (renameˢ ρ A)) [ ｀ Zˢ ]ᵗ) ⊑
              T)
          (renameˢ-ext-⇑ˢ ρ B)
          (Eq.subst
            (λ T →
              renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
                T ⊑
                renameˢ (extˢ ρ) (⇑ˢ B))
            (trans
              (renameˢ-[]ᵗ-seal (extˢ ρ) (⇑ˢ A) Zˢ)
              (cong (λ T → T [ ｀ Zˢ ]ᵗ) (renameˢ-ext-⇑ˢ ρ A)))
            (⊑-renameˢ (extˢ ρ) c))))

  ⊑-renameˢ :
    ∀{Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (ρ : Renameˢ Ψ Ψ′) →
    Σ ⊢ A ⊑ B →
    renameStoreˢ ρ Σ ⊢ renameˢ ρ A ⊑ renameˢ ρ B
  ⊑-renameˢ ρ id = id
  ⊑-renameˢ ρ (p ； a) =
    (⊑-renameˢ ρ p) ； (⊑ᵃ-renameˢ ρ a)

mutual
  ⊑ᵃ-substᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (σ : Substᵗ Δ Δ′ Ψ) →
    Σ ⊢ A ⊑ᵃ B →
    Σ ⊢ substᵗ σ A ⊑ᵃ substᵗ σ B
  ⊑ᵃ-substᵗ σ (tag g) = tag (substᵗ-ground σ g)
  ⊑ᵃ-substᵗ σ (seal {α = α} {A = A} h) =
    Eq.subst
      (λ T → _ ⊢ T ⊑ᵃ ｀ α)
      (Eq.sym (substᵗ-wkTy0 σ A))
      (seal h)
  ⊑ᵃ-substᵗ σ (_↦_ {A = A} {A′ = A′} {B = B} {B′ = B′} p q) =
    _↦_ {A = substᵗ σ A}
        {A′ = substᵗ σ A′}
        {B = substᵗ σ B}
        {B′ = substᵗ σ B′}
      (⊑-substᵗ σ p)
      (⊑-substᵗ σ q)
  ⊑ᵃ-substᵗ σ (∀ᵖ p) =
    ∀ᵖ (⊑-substᵗ (extsᵗ σ) p)
  ⊑ᵃ-substᵗ {Σ = Σ} {A = `∀ A} {B = B} σ (ν c) =
    ν
      (Eq.subst
        (λ T →
          ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
            ((⇑ˢ (substᵗ (extsᵗ σ) A)) [ ｀ Zˢ ]ᵗ) ⊑
            T)
        cod-eq
        (Eq.subst
          (λ T →
            ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢
              T ⊑
              substᵗ liftσ (⇑ˢ B))
          dom-eq
          (⊑-substᵗ liftσ c)))
    where
      liftσ : Substᵗ _ _ (suc _)
      liftσ = liftSubstˢ σ

      inner-eq :
        substᵗ (extsᵗ liftσ) (⇑ˢ A) ≡
        ⇑ˢ (substᵗ (extsᵗ σ) A)
      inner-eq =
        trans
          (substᵗ-cong (exts-liftSubstˢ σ) (⇑ˢ A))
          (substᵗ-⇑ˢ (extsᵗ σ) A)

      dom-eq :
        substᵗ liftσ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ≡
        ((⇑ˢ (substᵗ (extsᵗ σ) A)) [ ｀ Zˢ ]ᵗ)
      dom-eq =
        trans
          (substᵗ-[]ᵗ-seal liftσ (⇑ˢ A) Zˢ)
          (cong (λ T → T [ ｀ Zˢ ]ᵗ) inner-eq)

      cod-eq :
        substᵗ liftσ (⇑ˢ B) ≡
        (⇑ˢ (substᵗ σ B))
      cod-eq = substᵗ-⇑ˢ σ B

  ⊑-substᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
    (σ : Substᵗ Δ Δ′ Ψ) →
    Σ ⊢ A ⊑ B →
    Σ ⊢ substᵗ σ A ⊑ substᵗ σ B
  ⊑-substᵗ σ id = id
  ⊑-substᵗ σ (p ； a) = (⊑-substᵗ σ p) ； (⊑ᵃ-substᵗ σ a)

⊑-[]ᵗ-seal :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty (suc Δ) Ψ}{α : Seal Ψ} →
  Σ ⊢ A ⊑ B →
  Σ ⊢ A [ ｀ α ]ᵗ ⊑ B [ ｀ α ]ᵗ
⊑-[]ᵗ-seal {α = α} p =
  ⊑-substᵗ (singleTyEnv (｀ α)) p

⊑-shift★ :
  ∀{Δ}{Ψ}{Σ : Store Ψ}{A B : Ty Δ Ψ} →
  Σ ⊢ A ⊑ B →
  ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ⇑ˢ A ⊑ ⇑ˢ B
⊑-shift★ p =
  ⊑-wkΣ (drop ⊆ˢ-refl) (⊑-renameˢ Sˢ p)
