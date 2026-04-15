module UpDownNorm where

-- File Charter:
--   * Normalized Up/Down syntax without a generic composition constructor.
--   * Composition is represented at primitive boundaries (tag/untag, seal/unseal).
--   * Provides typing judgments plus composition operators and closure statements.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using (List; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product as Prod using (Σ; ∃; ∃-syntax; _,_; proj₁; proj₂)

open import Types
open import TypeProperties
open import Store
open import UpDown
  using
    ( Label
    ; CastPerm
    ; cast-tag ; cast-seal ; conv
    ; _∈_ ; here-conv ; here-seal ; there
    ; _∈conv_ ; here-conv-only ; there-conv
    ; _∈cast_ ; here-cast-only ; there-cast
    ; _∈tag_ ; here-tag-only ; there-tag
    ; _∉_
    ; ∈conv⇒∈ ; ∈cast⇒∈
    ; ⊢_ok_
    ; WfTySome
    ; wfTySome
    ; lookupTyˢ
    )

infixr 7 _↦_
infixl 6 _；tag_ untag_[_]；_ _；seal_
infixr 6 unseal_；_

mutual
  data Up : Set where
    _；tag_ : Up → Ty → Up
    unseal_；_ : Seal → Up → Up
    _↦_ : Down → Up → Up
    ∀ᵖ : Up → Up
    ν_ : Up → Up
    id : Ty → Up

  data Down : Set where
    untag_[_]；_ : Ty → Label → Down → Down
    _；seal_ : Down → Seal → Down
    _↦_ : Up → Down → Down
    ∀ᵖ : Down → Down
    ν_ : Down → Down
    id : Ty → Down

mutual
  rename⊑ᵗ : (ρ : Renameᵗ) → Up → Up
  rename⊑ᵗ ρ (p ；tag G) = (rename⊑ᵗ ρ p) ；tag (renameᵗ ρ G)
  rename⊑ᵗ ρ (unseal α ； q) = unseal α ； (rename⊑ᵗ ρ q)
  rename⊑ᵗ ρ (p ↦ q) = rename⊒ᵗ ρ p ↦ rename⊑ᵗ ρ q
  rename⊑ᵗ ρ (∀ᵖ p) = ∀ᵖ (rename⊑ᵗ (extᵗ ρ) p)
  rename⊑ᵗ ρ (ν p) = ν (rename⊑ᵗ ρ p)
  rename⊑ᵗ ρ (id A) = id (renameᵗ ρ A)

  rename⊒ᵗ : (ρ : Renameᵗ) → Down → Down
  rename⊒ᵗ ρ (untag G [ ℓ ]； q) = untag (renameᵗ ρ G) [ ℓ ]； (rename⊒ᵗ ρ q)
  rename⊒ᵗ ρ (p ；seal α) = (rename⊒ᵗ ρ p) ；seal α
  rename⊒ᵗ ρ (p ↦ q) = rename⊑ᵗ ρ p ↦ rename⊒ᵗ ρ q
  rename⊒ᵗ ρ (∀ᵖ p) = ∀ᵖ (rename⊒ᵗ (extᵗ ρ) p)
  rename⊒ᵗ ρ (ν p) = ν (rename⊒ᵗ ρ p)
  rename⊒ᵗ ρ (id A) = id (renameᵗ ρ A)

mutual
  rename⊑ˢ : (ρ : Renameˢ) → Up → Up
  rename⊑ˢ ρ (p ；tag G) = (rename⊑ˢ ρ p) ；tag (renameˢ ρ G)
  rename⊑ˢ ρ (unseal α ； q) = unseal (ρ α) ； (rename⊑ˢ ρ q)
  rename⊑ˢ ρ (p ↦ q) = rename⊒ˢ ρ p ↦ rename⊑ˢ ρ q
  rename⊑ˢ ρ (∀ᵖ p) = ∀ᵖ (rename⊑ˢ ρ p)
  rename⊑ˢ ρ (ν p) = ν (rename⊑ˢ (extˢ ρ) p)
  rename⊑ˢ ρ (id A) = id (renameˢ ρ A)

  rename⊒ˢ : (ρ : Renameˢ) → Down → Down
  rename⊒ˢ ρ (untag G [ ℓ ]； q) = untag (renameˢ ρ G) [ ℓ ]； (rename⊒ˢ ρ q)
  rename⊒ˢ ρ (p ；seal α) = (rename⊒ˢ ρ p) ；seal (ρ α)
  rename⊒ˢ ρ (p ↦ q) = rename⊑ˢ ρ p ↦ rename⊒ˢ ρ q
  rename⊒ˢ ρ (∀ᵖ p) = ∀ᵖ (rename⊒ˢ ρ p)
  rename⊒ˢ ρ (ν p) = ν (rename⊒ˢ (extˢ ρ) p)
  rename⊒ˢ ρ (id A) = id (renameˢ ρ A)


↑⊑ˢ : Up → Up
↑⊑ˢ p = rename⊑ˢ suc p

↑⊒ˢ : Down → Down
↑⊒ˢ p = rename⊒ˢ suc p

mutual
  subst⊑ᵗ : (σ : Substᵗ) → Up → Up
  subst⊑ᵗ σ (p ；tag G) = (subst⊑ᵗ σ p) ；tag (substᵗ σ G)
  subst⊑ᵗ σ (unseal α ； q) = unseal α ； (subst⊑ᵗ σ q)
  subst⊑ᵗ σ (p ↦ q) = subst⊒ᵗ σ p ↦ subst⊑ᵗ σ q
  subst⊑ᵗ σ (∀ᵖ p) = ∀ᵖ (subst⊑ᵗ (extsᵗ σ) p)
  subst⊑ᵗ σ (ν p) = ν (subst⊑ᵗ (liftSubstˢ σ) p)
  subst⊑ᵗ σ (id A) = id (substᵗ σ A)

  subst⊒ᵗ : (σ : Substᵗ) → Down → Down
  subst⊒ᵗ σ (untag G [ ℓ ]； q) = untag (substᵗ σ G) [ ℓ ]； (subst⊒ᵗ σ q)
  subst⊒ᵗ σ (p ；seal α) = (subst⊒ᵗ σ p) ；seal α
  subst⊒ᵗ σ (p ↦ q) = subst⊑ᵗ σ p ↦ subst⊒ᵗ σ q
  subst⊒ᵗ σ (∀ᵖ p) = ∀ᵖ (subst⊒ᵗ (extsᵗ σ) p)
  subst⊒ᵗ σ (ν p) = ν (subst⊒ᵗ (liftSubstˢ σ) p)
  subst⊒ᵗ σ (id A) = id (substᵗ σ A)

infixl 8 _[_]⊑
_[_]⊑ : Up → Ty → Up
p [ A ]⊑ = subst⊑ᵗ (singleTyEnv A) p

infixl 8 _[_]⊒
_[_]⊒ : Down → Ty → Down
p [ A ]⊒ = subst⊒ᵗ (singleTyEnv A) p

mutual
  up-src : Store → Up → Ty
  up-src Σ (p ；tag G) = up-src Σ p
  up-src Σ (unseal α ； p) = ｀ α
  up-src Σ (p ↦ q) = down-tgt Σ p ⇒ up-src Σ q
  up-src Σ (∀ᵖ p) = `∀ (up-src (⟰ᵗ Σ) p)
  up-src Σ (ν p) = `∀ ((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ)
  up-src Σ (id A) = A

  up-tgt : Store → Up → Ty
  up-tgt Σ (p ；tag G) = ★
  up-tgt Σ (unseal α ； p) = up-tgt Σ p
  up-tgt Σ (p ↦ q) = down-src Σ p ⇒ up-tgt Σ q
  up-tgt Σ (∀ᵖ p) = `∀ (up-tgt (⟰ᵗ Σ) p)
  up-tgt Σ (ν p) = renameˢ (singleSealEnv zero) (up-tgt ((zero , ★) ∷ ⟰ˢ Σ) p)
  up-tgt Σ (id A) = A

  down-src : Store → Down → Ty
  down-src Σ (untag G [ ℓ ]； p) = ★
  down-src Σ (p ；seal α) = down-src Σ p
  down-src Σ (p ↦ q) = up-tgt Σ p ⇒ down-src Σ q
  down-src Σ (∀ᵖ p) = `∀ (down-src (⟰ᵗ Σ) p)
  down-src Σ (ν p) = renameˢ (singleSealEnv zero) (down-src ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) p)
  down-src Σ (id A) = A

  down-tgt : Store → Down → Ty
  down-tgt Σ (untag G [ ℓ ]； p) = down-tgt Σ p
  down-tgt Σ (p ；seal α) = ｀ α
  down-tgt Σ (p ↦ q) = up-src Σ p ⇒ down-tgt Σ q
  down-tgt Σ (∀ᵖ p) = `∀ (down-tgt (⟰ᵗ Σ) p)
  down-tgt Σ (ν p) = `∀ ((⇑ᵗ (down-tgt ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ)
  down-tgt Σ (id A) = A

infix 3 _∣_⊢_⦂_⊑_ _∣_⊢_⦂_⊒_

mutual
  data _∣_⊢_⦂_⊑_ (Σ : Store) (Φ : List CastPerm) : Up → Ty → Ty → Set where
    wt-；tag : ∀ {A G}{p : Up}
      → Σ ∣ Φ ⊢ p ⦂ A ⊑ G
      → (g : Ground G)
      → ⊢ g ok Φ
      → Σ ∣ Φ ⊢ p ；tag G ⦂ A ⊑ ★

    wt-unseal； : ∀ {α A B}{p : Up}
      → Σ ∋ˢ α ⦂ A
      → α ∈conv Φ
      → Σ ∣ Φ ⊢ p ⦂ A ⊑ B
      → Σ ∣ Φ ⊢ unseal α ； p ⦂ ｀ α ⊑ B

    wt-unseal★； : ∀ {α B}{p : Up}
      → Σ ∋ˢ α ⦂ ★
      → α ∈cast Φ
      → Σ ∣ Φ ⊢ p ⦂ ★ ⊑ B
      → Σ ∣ Φ ⊢ unseal α ； p ⦂ ｀ α ⊑ B

    wt-↦ : ∀ {A A′ B B′}{p : Down}{q : Up}
      → Σ ∣ Φ ⊢ p ⦂ A′ ⊒ A
      → Σ ∣ Φ ⊢ q ⦂ B ⊑ B′
      → Σ ∣ Φ ⊢ p ↦ q ⦂ (A ⇒ B) ⊑ (A′ ⇒ B′)

    wt-∀ : ∀ {A B}{p : Up}
      → ⟰ᵗ Σ ∣ Φ ⊢ p ⦂ A ⊑ B
      → Σ ∣ Φ ⊢ ∀ᵖ p ⦂ `∀ A ⊑ `∀ B

    wt-ν : ∀ {A B}{p : Up}
      → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ p ⦂ (⇑ˢ A) [ ｀ zero ]ᵗ ⊑ ⇑ˢ B
      → Σ ∣ Φ ⊢ ν p ⦂ `∀ A ⊑ B

    wt-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ id A ⦂ A ⊑ A

  data _∣_⊢_⦂_⊒_ (Σ : Store) (Φ : List CastPerm) : Down → Ty → Ty → Set where
    wt-untag； : ∀ {G B}{p : Down}
      → (g : Ground G)
      → ⊢ g ok Φ
      → (ℓ : Label)
      → Σ ∣ Φ ⊢ p ⦂ G ⊒ B
      → Σ ∣ Φ ⊢ untag G [ ℓ ]； p ⦂ ★ ⊒ B

    wt-；seal : ∀ {A α}{p : Down}
      → Σ ∣ Φ ⊢ p ⦂ A ⊒ lookupTyˢ Σ α
      → Σ ∋ˢ α ⦂ lookupTyˢ Σ α
      → α ∈conv Φ
      → Σ ∣ Φ ⊢ p ；seal α ⦂ A ⊒ ｀ α

    wt-；seal★ : ∀ {A α}{p : Down}
      → Σ ∣ Φ ⊢ p ⦂ A ⊒ ★
      → Σ ∋ˢ α ⦂ ★
      → α ∈cast Φ
      → Σ ∣ Φ ⊢ p ；seal α ⦂ A ⊒ ｀ α

    wt-↦ : ∀ {A A′ B B′}{p : Up}{q : Down}
      → Σ ∣ Φ ⊢ p ⦂ A′ ⊑ A
      → Σ ∣ Φ ⊢ q ⦂ B ⊒ B′
      → Σ ∣ Φ ⊢ p ↦ q ⦂ (A ⇒ B) ⊒ (A′ ⇒ B′)

    wt-∀ : ∀ {A B}{p : Down}
      → ⟰ᵗ Σ ∣ Φ ⊢ p ⦂ A ⊒ B
      → Σ ∣ Φ ⊢ ∀ᵖ p ⦂ `∀ A ⊒ `∀ B

    wt-ν : ∀ {A B}{p : Down}
      → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ p ⦂ ⇑ˢ B ⊒ (⇑ˢ A) [ ｀ zero ]ᵗ
      → Σ ∣ Φ ⊢ ν p ⦂ B ⊒ `∀ A

    wt-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ id A ⦂ A ⊒ A

mutual
  size↑ : Up → ℕ
  size↑ (p ；tag G) = suc (size↑ p)
  size↑ (unseal α ； p) = suc (size↑ p)
  size↑ (p ↦ q) = suc (size↓ p + size↑ q)
  size↑ (∀ᵖ p) = suc (size↑ p)
  size↑ (ν p) = suc (size↑ p)
  size↑ (id A) = suc zero

  size↓ : Down → ℕ
  size↓ (untag G [ ℓ ]； p) = suc (size↓ p)
  size↓ (p ；seal α) = suc (size↓ p)
  size↓ (p ↦ q) = suc (size↑ p + size↓ q)
  size↓ (∀ᵖ p) = suc (size↓ p)
  size↓ (ν p) = suc (size↓ p)
  size↓ (id A) = suc zero

mutual
  size↑-rename⊑ᵗ : (ρ : Renameᵗ) → (p : Up) → size↑ (rename⊑ᵗ ρ p) ≡ size↑ p
  size↑-rename⊑ᵗ ρ (p ；tag G)
    rewrite size↑-rename⊑ᵗ ρ p = refl
  size↑-rename⊑ᵗ ρ (unseal α ； p)
    rewrite size↑-rename⊑ᵗ ρ p = refl
  size↑-rename⊑ᵗ ρ (p ↦ q)
    rewrite size↓-rename⊒ᵗ ρ p | size↑-rename⊑ᵗ ρ q = refl
  size↑-rename⊑ᵗ ρ (∀ᵖ p)
    rewrite size↑-rename⊑ᵗ (extᵗ ρ) p = refl
  size↑-rename⊑ᵗ ρ (ν p)
    rewrite size↑-rename⊑ᵗ ρ p = refl
  size↑-rename⊑ᵗ ρ (id A) = refl

  size↓-rename⊒ᵗ : (ρ : Renameᵗ) → (p : Down) → size↓ (rename⊒ᵗ ρ p) ≡ size↓ p
  size↓-rename⊒ᵗ ρ (untag G [ ℓ ]； p)
    rewrite size↓-rename⊒ᵗ ρ p = refl
  size↓-rename⊒ᵗ ρ (p ；seal α)
    rewrite size↓-rename⊒ᵗ ρ p = refl
  size↓-rename⊒ᵗ ρ (p ↦ q)
    rewrite size↑-rename⊑ᵗ ρ p | size↓-rename⊒ᵗ ρ q = refl
  size↓-rename⊒ᵗ ρ (∀ᵖ p)
    rewrite size↓-rename⊒ᵗ (extᵗ ρ) p = refl
  size↓-rename⊒ᵗ ρ (ν p)
    rewrite size↓-rename⊒ᵗ ρ p = refl
  size↓-rename⊒ᵗ ρ (id A) = refl

mutual
  size↑-rename⊑ˢ : (ρ : Renameˢ) → (p : Up) → size↑ (rename⊑ˢ ρ p) ≡ size↑ p
  size↑-rename⊑ˢ ρ (p ；tag G)
    rewrite size↑-rename⊑ˢ ρ p = refl
  size↑-rename⊑ˢ ρ (unseal α ； p)
    rewrite size↑-rename⊑ˢ ρ p = refl
  size↑-rename⊑ˢ ρ (p ↦ q)
    rewrite size↓-rename⊒ˢ ρ p | size↑-rename⊑ˢ ρ q = refl
  size↑-rename⊑ˢ ρ (∀ᵖ p)
    rewrite size↑-rename⊑ˢ ρ p = refl
  size↑-rename⊑ˢ ρ (ν p)
    rewrite size↑-rename⊑ˢ (extˢ ρ) p = refl
  size↑-rename⊑ˢ ρ (id A) = refl

  size↓-rename⊒ˢ : (ρ : Renameˢ) → (p : Down) → size↓ (rename⊒ˢ ρ p) ≡ size↓ p
  size↓-rename⊒ˢ ρ (untag G [ ℓ ]； p)
    rewrite size↓-rename⊒ˢ ρ p = refl
  size↓-rename⊒ˢ ρ (p ；seal α)
    rewrite size↓-rename⊒ˢ ρ p = refl
  size↓-rename⊒ˢ ρ (p ↦ q)
    rewrite size↑-rename⊑ˢ ρ p | size↓-rename⊒ˢ ρ q = refl
  size↓-rename⊒ˢ ρ (∀ᵖ p)
    rewrite size↓-rename⊒ˢ ρ p = refl
  size↓-rename⊒ˢ ρ (ν p)
    rewrite size↓-rename⊒ˢ (extˢ ρ) p = refl
  size↓-rename⊒ˢ ρ (id A) = refl

mutual
  size↑-subst⊑ᵗ : (σ : Substᵗ) → (p : Up) → size↑ (subst⊑ᵗ σ p) ≡ size↑ p
  size↑-subst⊑ᵗ σ (p ；tag G)
    rewrite size↑-subst⊑ᵗ σ p = refl
  size↑-subst⊑ᵗ σ (unseal α ； p)
    rewrite size↑-subst⊑ᵗ σ p = refl
  size↑-subst⊑ᵗ σ (p ↦ q)
    rewrite size↓-subst⊒ᵗ σ p | size↑-subst⊑ᵗ σ q = refl
  size↑-subst⊑ᵗ σ (∀ᵖ p)
    rewrite size↑-subst⊑ᵗ (extsᵗ σ) p = refl
  size↑-subst⊑ᵗ σ (ν p)
    rewrite size↑-subst⊑ᵗ (liftSubstˢ σ) p = refl
  size↑-subst⊑ᵗ σ (id A) = refl

  size↓-subst⊒ᵗ : (σ : Substᵗ) → (p : Down) → size↓ (subst⊒ᵗ σ p) ≡ size↓ p
  size↓-subst⊒ᵗ σ (untag G [ ℓ ]； p)
    rewrite size↓-subst⊒ᵗ σ p = refl
  size↓-subst⊒ᵗ σ (p ；seal α)
    rewrite size↓-subst⊒ᵗ σ p = refl
  size↓-subst⊒ᵗ σ (p ↦ q)
    rewrite size↑-subst⊑ᵗ σ p | size↓-subst⊒ᵗ σ q = refl
  size↓-subst⊒ᵗ σ (∀ᵖ p)
    rewrite size↓-subst⊒ᵗ (extsᵗ σ) p = refl
  size↓-subst⊒ᵗ σ (ν p)
    rewrite size↓-subst⊒ᵗ (liftSubstˢ σ) p = refl
  size↓-subst⊒ᵗ σ (id A) = refl

size↑-↑⊑ˢ : (p : Up) → size↑ (↑⊑ˢ p) ≡ size↑ p
size↑-↑⊑ˢ p = size↑-rename⊑ˢ suc p

size↓-↑⊒ˢ : (p : Down) → size↓ (↑⊒ˢ p) ≡ size↓ p
size↓-↑⊒ˢ p = size↓-rename⊒ˢ suc p

mutual
  ⨟↑-fuel : ℕ → Up → Up → Up
  ⨟↑-fuel zero p q = p
  ⨟↑-fuel (suc n) (id A) q = q
  ⨟↑-fuel (suc n) p (id A) = p
  ⨟↑-fuel (suc n) (p ↦ q) (r ↦ s) = (⨟↓-fuel n r p) ↦ (⨟↑-fuel n q s)
  ⨟↑-fuel (suc n) (∀ᵖ p) (∀ᵖ q) = ∀ᵖ (⨟↑-fuel n p q)
  ⨟↑-fuel (suc n) (∀ᵖ p) (ν q) = ν (⨟↑-fuel n ((↑⊑ˢ p) [ α₀ ]⊑) q)
  ⨟↑-fuel (suc n) (unseal α ； p) q = unseal α ； (⨟↑-fuel n p q)
  ⨟↑-fuel (suc n) (ν p) q = ν (⨟↑-fuel n p (↑⊑ˢ q))
  ⨟↑-fuel (suc n) p (q ；tag G) = (⨟↑-fuel n p q) ；tag G
  ⨟↑-fuel (suc n) p q = p

  ⨟↓-fuel : ℕ → Down → Down → Down
  ⨟↓-fuel zero p q = p
  ⨟↓-fuel (suc n) (id A) q = q
  ⨟↓-fuel (suc n) p (id A) = p
  ⨟↓-fuel (suc n) (p ↦ q) (r ↦ s) = (⨟↑-fuel n r p) ↦ (⨟↓-fuel n q s)
  ⨟↓-fuel (suc n) (∀ᵖ p) (∀ᵖ q) = ∀ᵖ (⨟↓-fuel n p q)
  ⨟↓-fuel (suc n) (ν p) (∀ᵖ q) = ν (⨟↓-fuel n p ((↑⊒ˢ q) [ α₀ ]⊒))
  ⨟↓-fuel (suc n) p (q ；seal α) = (⨟↓-fuel n p q) ；seal α
  ⨟↓-fuel (suc n) p (ν q) = ν (⨟↓-fuel n (↑⊒ˢ p) q)
  ⨟↓-fuel (suc n) (untag G [ ℓ ]； p) q = untag G [ ℓ ]； (⨟↓-fuel n p q)
  ⨟↓-fuel (suc n) p q = p

mutual
  _⨟↑_ : Up → Up → Up
  p ⨟↑ q = ⨟↑-fuel (suc (size↑ p + size↑ q)) p q

  _⨟↓_ : Down → Down → Down
  p ⨟↓ q = ⨟↓-fuel (suc (size↓ p + size↓ q)) p q

mutual
  wt-⨟↑ :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}{p : Up}{q : Up}
    → Σ ∣ Φ ⊢ p ⦂ A ⊑ B
    → Σ ∣ Φ ⊢ q ⦂ B ⊑ C
    → Σ ∣ Φ ⊢ p ⨟↑ q ⦂ A ⊑ C
  wt-⨟↑ ⊢p ⊢q = ?

  wt-⨟↓ :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}{p : Down}{q : Down}
    → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
    → Σ ∣ Φ ⊢ q ⦂ B ⊒ C
    → Σ ∣ Φ ⊢ p ⨟↓ q ⦂ A ⊒ C
  wt-⨟↓ ⊢p ⊢q = ?

