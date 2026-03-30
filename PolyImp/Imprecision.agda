module Imprecision where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)
  renaming (subst to substEq)

open import Types
open import TypeSubst

Label : Set
Label = ℕ

------------------------------------------------------------------------
-- Intrinsically typed polymorphic imprecision witnesses
------------------------------------------------------------------------

infixr 7 _↦_
infixl 6 _；_
infixr 6 _⨟_
infix 5 _⊢_⊑_
infix 5 _⊢_⊑ᵃ_

mutual
  data _⊢_⊑ᵃ_ {Δ}{Ψ} (Σ : Store Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
    tag : ∀{G}
      → Ground G
      → Label
      → Σ ⊢ G ⊑ᵃ `★

    `⊥ : ∀{A B}
      → Label
      → Σ ⊢ A ⊑ᵃ B

    seal : ∀{α}{A}
      → Σ ∋ˢ α ⦂ A
      → Σ ⊢ ｀ α ⊑ᵃ wkTy0 A

    _↦_ : ∀{A A′ B B′}
      → Σ ⊢ A′ ⊑ A
      → Σ ⊢ B ⊑ B′
      → Σ ⊢ (A ⇒ B) ⊑ᵃ (A′ ⇒ B′)

    ∀ᵖ : ∀{A B : Ty (suc Δ) Ψ}
      → Σ ⊢ A ⊑ B
      → Σ ⊢ (`∀ A) ⊑ᵃ (`∀ B)

    ν_ : ∀{A : Ty (suc Δ) Ψ}{B : Ty Δ Ψ}
      → ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ⊑ (⇑ˢ B)
      → Σ ⊢ (`∀ A) ⊑ᵃ B

  data _⊢_⊑_ {Δ}{Ψ} (Σ : Store Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
    id : ∀{A}
      → Σ ⊢ A ⊑ A

    _；_ : ∀{A B C}
      → Σ ⊢ A ⊑ B
      → Σ ⊢ B ⊑ᵃ C
      → Σ ⊢ A ⊑ C

_⨟_ : ∀{Δ}{Ψ}{Σ : Store Ψ}{A B C : Ty Δ Ψ}
  → Σ ⊢ A ⊑ B
  → Σ ⊢ B ⊑ C
  → Σ ⊢ A ⊑ C
p ⨟ id = p
p ⨟ (q ； a) = (p ⨟ q) ； a

castᵖ :
  ∀ {Δ}{Ψ}{Σ Σ′ : Store Ψ}
    {A A′ B B′ : Ty Δ Ψ} →
  Σ ≡ Σ′ →
  A ≡ A′ →
  B ≡ B′ →
  Σ ⊢ A ⊑ B →
  Σ′ ⊢ A′ ⊑ B′
castᵖ refl refl refl p = p

open-renᵗ-sucᵖ :
  ∀{Δ}{Ψ} →
  (A : Ty Δ Ψ) →
  (T : Ty Δ Ψ) →
  (renameᵗ Sᵗ A) [ T ]ᵗ ≡ A
open-renᵗ-sucᵖ A T =
  trans
    (substᵗ-renameᵗ Sᵗ (singleTyEnv T) A)
    (trans
      (substᵗ-cong (λ X → refl) A)
      (substᵗ-id A))

renameᵗ-[]ᵗ-sealᵖ :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (A : Ty (suc Δ) Ψ) (α : Seal Ψ) →
  renameᵗ ρ (A [ ｀ α ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ ｀ α ]ᵗ
renameᵗ-[]ᵗ-sealᵖ ρ A α =
  trans
    (renameᵗ-substᵗ ρ (singleTyEnv (｀ α)) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-renameᵗ (extᵗ ρ) (singleTyEnv (｀ α)) A)))
  where
    env :
      (X : TyVar (suc _)) →
      renameᵗ ρ (singleTyEnv (｀ α) X) ≡
      singleTyEnv (｀ α) (extᵗ ρ X)
    env Zᵗ = refl
    env (Sᵗ X) = refl

substᵗ-[]ᵗ-sealᵖ :
  ∀{Δ}{Δ′}{Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (A : Ty (suc Δ) Ψ) (α : Seal Ψ) →
  substᵗ σ (A [ ｀ α ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ ｀ α ]ᵗ
substᵗ-[]ᵗ-sealᵖ σ A α =
  trans
    (substᵗ-substᵗ σ (singleTyEnv (｀ α)) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-substᵗ (singleTyEnv (｀ α)) (extsᵗ σ) A)))
  where
    env :
      (X : TyVar (suc _)) →
      substᵗ σ (singleTyEnv (｀ α) X) ≡
      substᵗ (singleTyEnv (｀ α)) (extsᵗ σ X)
    env Zᵗ = refl
    env (Sᵗ X) = sym (open-renᵗ-sucᵖ (σ X) (｀ α))

renameˢ-[]ᵗ-sealᵖ :
  ∀{Δ}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (A : Ty (suc Δ) Ψ) (α : Seal Ψ) →
  renameˢ ρ (A [ ｀ α ]ᵗ) ≡ (renameˢ ρ A) [ ｀ (ρ α) ]ᵗ
renameˢ-[]ᵗ-sealᵖ ρ A α =
  trans
    (renameˢ-substᵗ ρ (singleTyEnv (｀ α)) A)
    (substᵗ-cong env (renameˢ ρ A))
  where
    env :
      (X : TyVar (suc _)) →
      renameˢ ρ (singleTyEnv (｀ α) X) ≡
      singleTyEnv (｀ (ρ α)) X
    env Zᵗ = refl
    env (Sᵗ X) = refl

renameˢ-ext-⇑ˢᵖ :
  ∀{Δ}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (A : Ty Δ Ψ) →
  renameˢ (extˢ ρ) (⇑ˢ A) ≡ ⇑ˢ (renameˢ ρ A)
renameˢ-ext-⇑ˢᵖ ρ (＇ X) = refl
renameˢ-ext-⇑ˢᵖ ρ (｀ α) = refl
renameˢ-ext-⇑ˢᵖ ρ (‵ ι) = refl
renameˢ-ext-⇑ˢᵖ ρ `★ = refl
renameˢ-ext-⇑ˢᵖ ρ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-ext-⇑ˢᵖ ρ A) (renameˢ-ext-⇑ˢᵖ ρ B)
renameˢ-ext-⇑ˢᵖ ρ (`∀ A) =
  cong `∀ (renameˢ-ext-⇑ˢᵖ ρ A)

renameStoreˢ-ext-⟰ˢᵖ :
  ∀{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (Σ : Store Ψ) →
  renameStoreˢ (extˢ ρ) (⟰ˢ Σ) ≡ ⟰ˢ (renameStoreˢ ρ Σ)
renameStoreˢ-ext-⟰ˢᵖ ρ [] = refl
renameStoreˢ-ext-⟰ˢᵖ ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-ext-⇑ˢᵖ ρ A))
    (renameStoreˢ-ext-⟰ˢᵖ ρ Σ)

exts-liftSubstˢᵖ :
  ∀{Δ}{Δ′}{Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (X : TyVar (suc Δ)) →
  extsᵗ (liftSubstˢ σ) X ≡ liftSubstˢ (extsᵗ σ) X
exts-liftSubstˢᵖ σ Zᵗ = refl
exts-liftSubstˢᵖ σ (Sᵗ X) = renameᵗ-⇑ˢ Sᵗ (σ X)

renameᵗ-ν-srcᵖ :
  ∀ {Δ}{Δ′}{Ψ} (ρ : Renameᵗ Δ Δ′) (A : Ty (suc Δ) Ψ) →
  renameᵗ ρ (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ≡
  ((⇑ˢ (renameᵗ (extᵗ ρ) A)) [ ｀ Zˢ ]ᵗ)
renameᵗ-ν-srcᵖ ρ A =
  trans
    (renameᵗ-[]ᵗ-sealᵖ ρ (⇑ˢ A) Zˢ)
    (cong (λ C → C [ ｀ Zˢ ]ᵗ) (renameᵗ-⇑ˢ (extᵗ ρ) A))

substᵗ-ν-srcᵖ :
  ∀ {Δ}{Δ′}{Ψ} (σ : Substᵗ Δ Δ′ Ψ) (A : Ty (suc Δ) Ψ) →
  substᵗ (liftSubstˢ σ) (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ≡
  ((⇑ˢ (substᵗ (extsᵗ σ) A)) [ ｀ Zˢ ]ᵗ)
substᵗ-ν-srcᵖ σ A =
  trans
    (substᵗ-[]ᵗ-sealᵖ (liftSubstˢ σ) (⇑ˢ A) Zˢ)
    (cong
      (λ C → C [ ｀ Zˢ ]ᵗ)
      (trans
        (substᵗ-cong (exts-liftSubstˢᵖ σ) (⇑ˢ A))
        (substᵗ-⇑ˢ (extsᵗ σ) A)))

renameˢ-ν-srcᵖ :
  ∀ {Δ}{Ψ}{Ψ′} (ρ : Renameˢ Ψ Ψ′) (A : Ty (suc Δ) Ψ) →
  renameˢ (extˢ ρ) (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ≡
  ((⇑ˢ (renameˢ ρ A)) [ ｀ Zˢ ]ᵗ)
renameˢ-ν-srcᵖ ρ A =
  trans
    (renameˢ-[]ᵗ-sealᵖ (extˢ ρ) (⇑ˢ A) Zˢ)
    (cong (λ C → C [ ｀ Zˢ ]ᵗ) (renameˢ-ext-⇑ˢᵖ ρ A))

renameStoreˢ-↑★ᵖ :
  ∀ {Ψ}{Ψ′} (ρ : Renameˢ Ψ Ψ′) (Σ : Store Ψ) →
  renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ≡
  (Zˢ , ⇑ˢ `★) ∷ ⟰ˢ (renameStoreˢ ρ Σ)
renameStoreˢ-↑★ᵖ ρ Σ =
  cong₂ _∷_
    (cong₂ _,_ refl (renameˢ-ext-⇑ˢᵖ ρ `★))
    (renameStoreˢ-ext-⟰ˢᵖ ρ Σ)

------------------------------------------------------------------------
-- Type-variable renaming and substitution for imprecision
------------------------------------------------------------------------

mutual
  renameAtomᵖᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B}
    (ρ : Renameᵗ Δ Δ′) →
    Σ ⊢ A ⊑ᵃ B →
    Σ ⊢ renameᵗ ρ A ⊑ᵃ renameᵗ ρ B
  renameAtomᵖᵗ ρ (tag g ℓ) = tag (renameᵗ-ground ρ g) ℓ
  renameAtomᵖᵗ ρ (`⊥ ℓ) = `⊥ ℓ
  renameAtomᵖᵗ ρ (seal {A = A₀} h)
    rewrite renameᵗ-wkTy0 ρ A₀ = seal h
  renameAtomᵖᵗ ρ (p ↦ q) = renameᵖᵗ ρ p ↦ renameᵖᵗ ρ q
  renameAtomᵖᵗ ρ (∀ᵖ p) = ∀ᵖ (renameᵖᵗ (extᵗ ρ) p)
  renameAtomᵖᵗ {Σ = Σ} ρ (ν_ {A = A} {B = B} i) = ν i′
    where
      dom-eq :
        renameᵗ ρ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ≡
        ((⇑ˢ (renameᵗ (extᵗ ρ) A)) [ ｀ Zˢ ]ᵗ)
      dom-eq = renameᵗ-ν-srcᵖ ρ A

      cod-eq :
        renameᵗ ρ (⇑ˢ B) ≡
        (⇑ˢ (renameᵗ ρ B))
      cod-eq = renameᵗ-⇑ˢ ρ B

      i′ :
        ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ (renameᵗ (extᵗ ρ) A)) [ ｀ Zˢ ]ᵗ) ⊑
                                  (⇑ˢ (renameᵗ ρ B))
      i′ = castᵖ refl dom-eq cod-eq (renameᵖᵗ ρ i)

  renameᵖᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B}
    (ρ : Renameᵗ Δ Δ′) →
    Σ ⊢ A ⊑ B →
    Σ ⊢ renameᵗ ρ A ⊑ renameᵗ ρ B
  renameᵖᵗ ρ id = id
  renameᵖᵗ ρ (p ； a) = renameᵖᵗ ρ p ； renameAtomᵖᵗ ρ a

mutual
  substAtomᵖᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B}
    (σ : Substᵗ Δ Δ′ Ψ) →
    Σ ⊢ A ⊑ᵃ B →
    Σ ⊢ substᵗ σ A ⊑ᵃ substᵗ σ B
  substAtomᵖᵗ σ (tag g ℓ) = tag (substᵗ-ground σ g) ℓ
  substAtomᵖᵗ σ (`⊥ ℓ) = `⊥ ℓ
  substAtomᵖᵗ σ (seal {A = A₀} h)
    rewrite substᵗ-wkTy0 σ A₀ = seal h
  substAtomᵖᵗ σ (p ↦ q) = substᵖᵗ σ p ↦ substᵖᵗ σ q
  substAtomᵖᵗ σ (∀ᵖ p) = ∀ᵖ (substᵖᵗ (extsᵗ σ) p)
  substAtomᵖᵗ {Σ = Σ} σ (ν_ {A = A} {B = B} i) = ν i′
    where
      liftσ : Substᵗ _ _ (suc _)
      liftσ = liftSubstˢ σ

      dom-eq :
        substᵗ liftσ ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ≡
        ((⇑ˢ (substᵗ (extsᵗ σ) A)) [ ｀ Zˢ ]ᵗ)
      dom-eq = substᵗ-ν-srcᵖ σ A

      cod-eq :
        substᵗ liftσ (⇑ˢ B) ≡
        (⇑ˢ (substᵗ σ B))
      cod-eq = substᵗ-⇑ˢ σ B

      i′ :
        ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ⊢ ((⇑ˢ (substᵗ (extsᵗ σ) A)) [ ｀ Zˢ ]ᵗ) ⊑
                                  (⇑ˢ (substᵗ σ B))
      i′ = castᵖ refl dom-eq cod-eq (substᵖᵗ liftσ i)

  substᵖᵗ :
    ∀{Δ}{Δ′}{Ψ}{Σ : Store Ψ}{A B}
    (σ : Substᵗ Δ Δ′ Ψ) →
    Σ ⊢ A ⊑ B →
    Σ ⊢ substᵗ σ A ⊑ substᵗ σ B
  substᵖᵗ σ id = id
  substᵖᵗ σ (p ； a) = substᵖᵗ σ p ； substAtomᵖᵗ σ a

infixl 8 _[_]ᵖᵗ
_[_]ᵖᵗ :
  ∀ {Δ}{Ψ}{Σ : Store Ψ}{A B : Ty (suc Δ) Ψ}
  → Σ ⊢ A ⊑ B
  → (T : Ty Δ Ψ)
  → Σ ⊢ (A [ T ]ᵗ) ⊑ (B [ T ]ᵗ)
p [ T ]ᵖᵗ = substᵖᵗ (singleTyEnv T) p

------------------------------------------------------------------------
-- Seal renaming for imprecision
------------------------------------------------------------------------

mutual
  renameAtomᵖˢ :
    ∀{Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ}
    (ρ : Renameˢ Ψ Ψ′) →
    Σ ⊢ A ⊑ᵃ B →
    renameStoreˢ ρ Σ ⊢ renameˢ ρ A ⊑ᵃ renameˢ ρ B
  renameAtomᵖˢ ρ (tag g ℓ) = tag (renameˢ-ground ρ g) ℓ
  renameAtomᵖˢ ρ (`⊥ ℓ) = `⊥ ℓ
  renameAtomᵖˢ {Σ = Σ} ρ (seal {α = α} {A = A₀} h) =
    substEq
      (λ T → renameStoreˢ ρ Σ ⊢ ｀ (ρ α) ⊑ᵃ T)
      (sym (renameˢ-wkTy0 ρ A₀))
      (seal (renameLookupˢ ρ h))
  renameAtomᵖˢ ρ (p ↦ q) = renameᵖˢ ρ p ↦ renameᵖˢ ρ q
  renameAtomᵖˢ ρ (∀ᵖ p) = ∀ᵖ (renameᵖˢ ρ p)
  renameAtomᵖˢ {Σ = Σ} ρ (ν_ {A = A} {B = B} i) = ν i′
    where
      Σ-eq :
        renameStoreˢ (extˢ ρ) ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ) ≡
        ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ (renameStoreˢ ρ Σ))
      Σ-eq = renameStoreˢ-↑★ᵖ ρ Σ

      dom-eq :
        renameˢ (extˢ ρ) ((⇑ˢ A) [ ｀ Zˢ ]ᵗ) ≡
        ((⇑ˢ (renameˢ ρ A)) [ ｀ Zˢ ]ᵗ)
      dom-eq = renameˢ-ν-srcᵖ ρ A

      cod-eq :
        renameˢ (extˢ ρ) (⇑ˢ B) ≡
        (⇑ˢ (renameˢ ρ B))
      cod-eq = renameˢ-ext-⇑ˢᵖ ρ B

      i′ :
        ((Zˢ , ⇑ˢ `★) ∷ ⟰ˢ (renameStoreˢ ρ Σ)) ⊢ ((⇑ˢ (renameˢ ρ A)) [ ｀ Zˢ ]ᵗ) ⊑
                                                     (⇑ˢ (renameˢ ρ B))
      i′ = castᵖ Σ-eq dom-eq cod-eq (renameᵖˢ (extˢ ρ) i)

  renameᵖˢ :
    ∀{Δ}{Ψ}{Ψ′}{Σ : Store Ψ}{A B : Ty Δ Ψ}
    (ρ : Renameˢ Ψ Ψ′) →
    Σ ⊢ A ⊑ B →
    renameStoreˢ ρ Σ ⊢ renameˢ ρ A ⊑ renameˢ ρ B
  renameᵖˢ ρ id = id
  renameᵖˢ ρ (p ； a) = renameᵖˢ ρ p ； renameAtomᵖˢ ρ a
