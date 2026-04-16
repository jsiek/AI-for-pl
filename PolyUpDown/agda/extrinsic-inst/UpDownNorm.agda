module UpDownNorm where

-- File Charter:
--   * Normalized Up/Down syntax without a generic composition constructor.
--   * Composition is represented at primitive boundaries (tag/untag, seal/unseal).
--   * Provides typing judgments, composition operators, closure statements, and substitution.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using (List; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; s≤s⁻¹)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; trans)
open import Data.Nat.Properties
  using
    ( ≤-refl
    ; ≤-trans
    ; +-suc
    ; +-identityʳ
    ; +-assoc
    ; +-comm
    ; +-mono-≤
    ; m≤m+n
    ; m≤n+m
    )
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
    )
open import TermProperties using (substStoreᵗ-singleTyEnv-⟰ᵗ)

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

    wt-；seal : ∀ {A B α}{p : Down}
      → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
      → Σ ∋ˢ α ⦂ B
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

pred-tag-bound↑ :
  ∀ {n : ℕ}{p q : Up}{G : Ty}
  → suc (size↑ p + size↑ (q ；tag G)) ≤ suc n
  → suc (size↑ p + size↑ q) ≤ n
pred-tag-bound↑ {p = p} {q = q} h
  rewrite +-suc (size↑ p) (size↑ q) = s≤s⁻¹ h

pred-seal-bound↓ :
  ∀ {n : ℕ}{p q : Down}{α : Seal}
  → suc (size↓ p + size↓ (q ；seal α)) ≤ suc n
  → suc (size↓ p + size↓ q) ≤ n
pred-seal-bound↓ {p = p} {q = q} h
  rewrite +-suc (size↓ p) (size↓ q) = s≤s⁻¹ h

weaken≤ : ∀ {m n : ℕ} → m ≤ n → m ≤ suc n
weaken≤ z≤n = z≤n
weaken≤ (s≤s h) = s≤s (weaken≤ h)

drop-suc≤ : ∀ {m n : ℕ} → suc m ≤ n → m ≤ n
drop-suc≤ {n = zero} ()
drop-suc≤ {n = suc n} h = weaken≤ (s≤s⁻¹ h)

pred-∀-bound↑ :
  ∀ {n : ℕ}{p q : Up}
  → suc (size↑ (∀ᵖ p) + size↑ (∀ᵖ q)) ≤ suc n
  → suc (size↑ p + size↑ q) ≤ n
pred-∀-bound↑ {p = p} {q = q} h
  rewrite +-suc (size↑ p) (size↑ q) = drop-suc≤ (s≤s⁻¹ h)

pred-∀-bound↓ :
  ∀ {n : ℕ}{p q : Down}
  → suc (size↓ (∀ᵖ p) + size↓ (∀ᵖ q)) ≤ suc n
  → suc (size↓ p + size↓ q) ≤ n
pred-∀-bound↓ {p = p} {q = q} h
  rewrite +-suc (size↓ p) (size↓ q) = drop-suc≤ (s≤s⁻¹ h)

pred-↦-sum-bound :
  ∀ {a b c d n : ℕ}
  → suc (suc (a + b) + suc (c + d)) ≤ suc n
  → suc ((a + b) + (c + d)) ≤ n
pred-↦-sum-bound {a} {b} {c} {d} h
  rewrite +-suc (a + b) (c + d) = drop-suc≤ (s≤s⁻¹ h)

pred-↦-bound-left :
  ∀ {a b c d n : ℕ}
  → suc (suc (a + b) + suc (c + d)) ≤ suc n
  → suc (c + a) ≤ n
pred-↦-bound-left {a} {b} {c} {d} h
  rewrite +-comm c a =
    ≤-trans
      (s≤s (+-mono-≤ (m≤m+n a b) (m≤m+n c d)))
      (pred-↦-sum-bound {a = a} {b = b} {c = c} {d = d} h)

pred-↦-bound-right :
  ∀ {a b c d n : ℕ}
  → suc (suc (a + b) + suc (c + d)) ≤ suc n
  → suc (b + d) ≤ n
pred-↦-bound-right {a} {b} {c} {d} h =
  ≤-trans
    (s≤s (+-mono-≤ (m≤n+m b a) (m≤n+m d c)))
    (pred-↦-sum-bound {a = a} {b = b} {c = c} {d = d} h)

pred-∀ν-bound↑ :
  ∀ {n : ℕ}{p q : Up}
  → suc (size↑ (∀ᵖ p) + size↑ (ν q)) ≤ suc n
  → suc (size↑ ((↑⊑ˢ p) [ α₀ ]⊑) + size↑ q) ≤ n
pred-∀ν-bound↑ {n = n} {p = p} {q = q} h
  rewrite size↑-subst⊑ᵗ (singleTyEnv α₀) (↑⊑ˢ p)
        | size↑-↑⊑ˢ p =
  pred-↦-sum-bound {a = zero} {b = size↑ p} {c = zero} {d = size↑ q} h

pred-ν∀-bound↓ :
  ∀ {n : ℕ}{p q : Down}
  → suc (size↓ (ν p) + size↓ (∀ᵖ q)) ≤ suc n
  → suc (size↓ p + size↓ ((↑⊒ˢ q) [ α₀ ]⊒)) ≤ n
pred-ν∀-bound↓ {n = n} {p = p} {q = q} h
  rewrite size↓-subst⊒ᵗ (singleTyEnv α₀) (↑⊒ˢ q)
        | size↓-↑⊒ˢ q =
  pred-↦-sum-bound {a = zero} {b = size↓ p} {c = zero} {d = size↓ q} h

pred-ν-bound↑ :
  ∀ {n : ℕ}{p q : Up}
  → suc (size↑ (ν p) + size↑ q) ≤ suc n
  → suc (size↑ p + size↑ (↑⊑ˢ q)) ≤ n
pred-ν-bound↑ {n = n} {p = p} {q = q} h
  rewrite size↑-↑⊑ˢ q =
  s≤s⁻¹ h

pred-ν-bound↓ :
  ∀ {n : ℕ}{p q : Down}
  → suc (size↓ p + size↓ (ν q)) ≤ suc n
  → suc (size↓ (↑⊒ˢ p) + size↓ q) ≤ n
pred-ν-bound↓ {n = n} {p = p} {q = q} h
  rewrite size↓-↑⊒ˢ p
        | +-suc (size↓ p) (size↓ q) =
  s≤s⁻¹ h

castWt⊑ :
  ∀ {Σ Σ′ : Store}{Φ Φ′ : List CastPerm}{A B : Ty}{p : Up} →
  Σ ≡ Σ′ →
  Φ ≡ Φ′ →
  Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
  Σ′ ∣ Φ′ ⊢ p ⦂ A ⊑ B
castWt⊑ refl refl h = h

castWt⊒ :
  ∀ {Σ Σ′ : Store}{Φ Φ′ : List CastPerm}{A B : Ty}{p : Down} →
  Σ ≡ Σ′ →
  Φ ≡ Φ′ →
  Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
  Σ′ ∣ Φ′ ⊢ p ⦂ A ⊒ B
castWt⊒ refl refl h = h

castWt⊑-raw :
  ∀ {Σ : Store}{Φ : List CastPerm}{A A′ B B′ : Ty}{p : Up} →
  A ≡ A′ →
  B ≡ B′ →
  Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
  Σ ∣ Φ ⊢ p ⦂ A′ ⊑ B′
castWt⊑-raw refl refl h = h

castWt⊒-raw :
  ∀ {Σ : Store}{Φ : List CastPerm}{A A′ B B′ : Ty}{p : Down} →
  A ≡ A′ →
  B ≡ B′ →
  Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
  Σ ∣ Φ ⊢ p ⦂ A′ ⊒ B′
castWt⊒-raw refl refl h = h

RenOk : Renameˢ → List CastPerm → List CastPerm → Set
RenOk ρ P P′ = ∀ {α} → α ∈ P → ρ α ∈ P′

RenOkConv : Renameˢ → List CastPerm → List CastPerm → Set
RenOkConv ρ P P′ = ∀ {α} → α ∈conv P → ρ α ∈conv P′

RenOkCast : Renameˢ → List CastPerm → List CastPerm → Set
RenOkCast ρ P P′ = ∀ {α} → α ∈cast P → ρ α ∈cast P′

RenOkTag : Renameˢ → List CastPerm → List CastPerm → Set
RenOkTag ρ P P′ = ∀ {α} → α ∈tag P → ρ α ∈tag P′

RenNotIn : Renameˢ → List CastPerm → List CastPerm → Set
RenNotIn ρ P P′ = ∀ {α} → α ∉ P → ρ α ∉ P′

RenOk-ext-cast-seal :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOk ρ P P′ →
  RenOk (extˢ ρ) (cast-seal ∷ P) (cast-seal ∷ P′)
RenOk-ext-cast-seal ok {zero} here-seal = here-seal
RenOk-ext-cast-seal ok {suc α} (there p) = there (ok p)

RenOk-ext-cast-tag :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOk ρ P P′ →
  RenOk (extˢ ρ) (cast-tag ∷ P) (cast-tag ∷ P′)
RenOk-ext-cast-tag ok {zero} ()
RenOk-ext-cast-tag ok {suc α} (there p) = there (ok p)

RenOkConv-ext-cast-seal :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkConv ρ P P′ →
  RenOkConv (extˢ ρ) (cast-seal ∷ P) (cast-seal ∷ P′)
RenOkConv-ext-cast-seal ok {zero} ()
RenOkConv-ext-cast-seal ok {suc α} (there-conv p) = there-conv (ok p)

RenOkConv-ext-cast-tag :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkConv ρ P P′ →
  RenOkConv (extˢ ρ) (cast-tag ∷ P) (cast-tag ∷ P′)
RenOkConv-ext-cast-tag ok {zero} ()
RenOkConv-ext-cast-tag ok {suc α} (there-conv p) = there-conv (ok p)

RenOkCast-ext-cast-seal :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkCast ρ P P′ →
  RenOkCast (extˢ ρ) (cast-seal ∷ P) (cast-seal ∷ P′)
RenOkCast-ext-cast-seal ok {zero} here-cast-only = here-cast-only
RenOkCast-ext-cast-seal ok {suc α} (there-cast p) = there-cast (ok p)

RenOkCast-ext-cast-tag :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkCast ρ P P′ →
  RenOkCast (extˢ ρ) (cast-tag ∷ P) (cast-tag ∷ P′)
RenOkCast-ext-cast-tag ok {zero} ()
RenOkCast-ext-cast-tag ok {suc α} (there-cast p) = there-cast (ok p)

RenOkTag-ext-cast-seal :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkTag ρ P P′ →
  RenOkTag (extˢ ρ) (cast-seal ∷ P) (cast-seal ∷ P′)
RenOkTag-ext-cast-seal ok {zero} ()
RenOkTag-ext-cast-seal ok {suc α} (there-tag p) = there-tag (ok p)

RenOkTag-ext-cast-tag :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenOkTag ρ P P′ →
  RenOkTag (extˢ ρ) (cast-tag ∷ P) (cast-tag ∷ P′)
RenOkTag-ext-cast-tag ok {zero} here-tag-only = here-tag-only
RenOkTag-ext-cast-tag ok {suc α} (there-tag p) = there-tag (ok p)

RenNotIn-ext-cast-seal :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenNotIn ρ P P′ →
  RenNotIn (extˢ ρ) (cast-seal ∷ P) (cast-seal ∷ P′)
RenNotIn-ext-cast-seal ok {zero} α∉seal _ = α∉seal here-seal
RenNotIn-ext-cast-seal ok {suc α} α∉seal (there p) =
  ok (λ α∈ → α∉seal (there α∈)) p

RenNotIn-ext-cast-tag :
  ∀ {ρ : Renameˢ} {P P′ : List CastPerm} →
  RenNotIn ρ P P′ →
  RenNotIn (extˢ ρ) (cast-tag ∷ P) (cast-tag ∷ P′)
RenNotIn-ext-cast-tag ok {zero} α∉tag ()
RenNotIn-ext-cast-tag ok {suc α} α∉tag (there p) =
  ok (λ α∈ → α∉tag (there α∈)) p

renameˢ-ground-ok :
  ∀ {G : Ty}
  (ρ : Renameˢ) {Φ Φ′ : List CastPerm} →
  RenOkTag ρ Φ Φ′ →
  (g : Ground G) →
  ⊢ g ok Φ →
  ⊢ renameˢ-ground ρ g ok Φ′
renameˢ-ground-ok ρ ok (｀ α) gok = ok gok
renameˢ-ground-ok ρ ok (‵ ι) gok = gok
renameˢ-ground-ok ρ ok ★⇒★ gok = gok

substᵗ-ground-ok :
  ∀ {G : Ty}
  (σ : Substᵗ) (g : Ground G) {Φ : List CastPerm} →
  ⊢ g ok Φ →
  ⊢ substᵗ-ground σ g ok Φ
substᵗ-ground-ok σ (｀ α) gok = gok
substᵗ-ground-ok σ (‵ ι) gok = gok
substᵗ-ground-ok σ ★⇒★ gok = gok

inst-⟰ᵗ-⊆ˢ :
  ∀ {Σ Σ′ : Store} →
  Σ ⊆ˢ Σ′ →
  ⟰ᵗ Σ ⊆ˢ ⟰ᵗ Σ′
inst-⟰ᵗ-⊆ˢ done = done
inst-⟰ᵗ-⊆ˢ (keep {α = α} {A = A} w) =
  keep {α = α} {A = renameᵗ suc A} (inst-⟰ᵗ-⊆ˢ w)
inst-⟰ᵗ-⊆ˢ (drop {α = α} {A = A} w) =
  drop {α = α} {A = renameᵗ suc A} (inst-⟰ᵗ-⊆ˢ w)

mutual
  wk⊑ :
    ∀ {Σ Σ′ : Store}{Φ : List CastPerm}{A B : Ty}{p : Up} →
    Σ ⊆ˢ Σ′ →
    Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    Σ′ ∣ Φ ⊢ p ⦂ A ⊑ B
  wk⊑ w (wt-；tag ⊢p g ok) = wt-；tag (wk⊑ w ⊢p) g ok
  wk⊑ w (wt-unseal； h α∈ ⊢p) = wt-unseal； (wkLookupˢ w h) α∈ (wk⊑ w ⊢p)
  wk⊑ w (wt-unseal★； h α∈ ⊢p) = wt-unseal★； (wkLookupˢ w h) α∈ (wk⊑ w ⊢p)
  wk⊑ w (wt-↦ ⊢p ⊢q) = wt-↦ (wk⊒ w ⊢p) (wk⊑ w ⊢q)
  wk⊑ w (wt-∀ ⊢p) = wt-∀ (wk⊑ (inst-⟰ᵗ-⊆ˢ w) ⊢p)
  wk⊑ w (wt-ν ⊢p) = wt-ν (wk⊑ (ν-⊆ˢ ★ w) ⊢p)
  wk⊑ w (wt-id wfA) = wt-id wfA

  wk⊒ :
    ∀ {Σ Σ′ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down} →
    Σ ⊆ˢ Σ′ →
    Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    Σ′ ∣ Φ ⊢ p ⦂ A ⊒ B
  wk⊒ w (wt-untag； g ok ℓ ⊢p) = wt-untag； g ok ℓ (wk⊒ w ⊢p)
  wk⊒ w (wt-；seal ⊢p h α∈) = wt-；seal (wk⊒ w ⊢p) (wkLookupˢ w h) α∈
  wk⊒ w (wt-；seal★ ⊢p h α∈) = wt-；seal★ ((wk⊒ w ⊢p)) (wkLookupˢ w h) α∈
  wk⊒ w (wt-↦ ⊢p ⊢q) = wt-↦ (wk⊑ w ⊢p) (wk⊒ w ⊢q)
  wk⊒ w (wt-∀ ⊢p) = wt-∀ (wk⊒ (inst-⟰ᵗ-⊆ˢ w) ⊢p)
  wk⊒ w (wt-ν ⊢p) = wt-ν (wk⊒ (ν-⊆ˢ ★ w) ⊢p)
  wk⊒ w (wt-id wfA) = wt-id wfA

mutual
  ⊑-renameˢ-wt :
    ∀ {Σ : Store}
      {Φ : List CastPerm}{Φ′ : List CastPerm}{A B : Ty}
      {p : Up} →
    (ρ : Renameˢ) →
    RenOk ρ Φ Φ′ →
    RenOkConv ρ Φ Φ′ →
    RenOkCast ρ Φ Φ′ →
    RenOkTag ρ Φ Φ′ →
    RenNotIn ρ Φ Φ′ →
    Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    renameStoreˢ ρ Σ ∣ Φ′ ⊢ rename⊑ˢ ρ p ⦂ renameˢ ρ A ⊑ renameˢ ρ B
  ⊑-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ (wt-；tag ⊢p g ok) =
    wt-；tag (⊑-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ ⊢p) (renameˢ-ground ρ g) (renameˢ-ground-ok ρ okTag g ok)
  ⊑-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ (wt-unseal； h α∈ ⊢p) =
    wt-unseal； (renameLookupˢ ρ h) (okConv α∈) (⊑-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ ⊢p)
  ⊑-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ (wt-unseal★； h α∈ ⊢p) =
    wt-unseal★； (renameLookupˢ ρ h) (okCast α∈) (⊑-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ ⊢p)
  ⊑-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ (wt-↦ ⊢p ⊢q) =
    wt-↦ (⊒-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ ⊢p) (⊑-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ ⊢q)
  ⊑-renameˢ-wt {Σ = Σ} ρ okΦ okConv okCast okTag ok¬Φ (wt-∀ ⊢p) =
    wt-∀
      (castWt⊑
        (renameStoreˢ-ext-⟰ᵗ ρ Σ)
        refl
        (⊑-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ ⊢p))
  ⊑-renameˢ-wt {Σ = Σ} ρ okΦ okConv okCast okTag ok¬Φ (wt-ν {A = A} {B = B} ⊢p) =
    wt-ν
      (castWt⊑
        (renameStoreˢ-cons-⟰ˢ ρ ★ Σ)
        refl
        (castWt⊑-raw
          (renameˢ-ν-src ρ A)
          (renameˢ-ext-⇑ˢ ρ B)
          (⊑-renameˢ-wt
            (extˢ ρ)
            (RenOk-ext-cast-seal okΦ)
            (RenOkConv-ext-cast-seal okConv)
            (RenOkCast-ext-cast-seal okCast)
            (RenOkTag-ext-cast-seal okTag)
            (RenNotIn-ext-cast-seal ok¬Φ)
            ⊢p)))
  ⊑-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ (wt-id {A = A} wfA) = wt-id (wfTySome (renameˢ ρ A))

  ⊒-renameˢ-wt :
    ∀ {Σ : Store}
      {Φ : List CastPerm}{Φ′ : List CastPerm}{A B : Ty}
      {p : Down} →
    (ρ : Renameˢ) →
    RenOk ρ Φ Φ′ →
    RenOkConv ρ Φ Φ′ →
    RenOkCast ρ Φ Φ′ →
    RenOkTag ρ Φ Φ′ →
    RenNotIn ρ Φ Φ′ →
    Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    renameStoreˢ ρ Σ ∣ Φ′ ⊢ rename⊒ˢ ρ p ⦂ renameˢ ρ A ⊒ renameˢ ρ B
  ⊒-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ (wt-untag； g ok ℓ ⊢p) =
    wt-untag； (renameˢ-ground ρ g) (renameˢ-ground-ok ρ okTag g ok) ℓ (⊒-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ ⊢p)
  ⊒-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ (wt-；seal ⊢p h α∈) =
    wt-；seal (⊒-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ ⊢p) (renameLookupˢ ρ h) (okConv α∈)
  ⊒-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ (wt-；seal★ ⊢p h α∈) =
    wt-；seal★ (⊒-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ ⊢p) (renameLookupˢ ρ h) (okCast α∈)
  ⊒-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ (wt-↦ ⊢p ⊢q) =
    wt-↦ (⊑-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ ⊢p) (⊒-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ ⊢q)
  ⊒-renameˢ-wt {Σ = Σ} ρ okΦ okConv okCast okTag ok¬Φ (wt-∀ ⊢p) =
    wt-∀
      (castWt⊒
        (renameStoreˢ-ext-⟰ᵗ ρ Σ)
        refl
        (⊒-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ ⊢p))
  ⊒-renameˢ-wt {Σ = Σ} ρ okΦ okConv okCast okTag ok¬Φ (wt-ν {A = A} {B = B} ⊢p) =
    wt-ν
      (castWt⊒
        (renameStoreˢ-cons-⟰ˢ ρ ★ Σ)
        refl
        (castWt⊒-raw
          (renameˢ-ext-⇑ˢ ρ B)
          (renameˢ-ν-src ρ A)
          (⊒-renameˢ-wt
            (extˢ ρ)
            (RenOk-ext-cast-tag okΦ)
            (RenOkConv-ext-cast-tag okConv)
            (RenOkCast-ext-cast-tag okCast)
            (RenOkTag-ext-cast-tag okTag)
            (RenNotIn-ext-cast-tag ok¬Φ)
            ⊢p)))
  ⊒-renameˢ-wt ρ okΦ okConv okCast okTag ok¬Φ (wt-id {A = A} wfA) = wt-id (wfTySome (renameˢ ρ A))

mutual
  ⊑-substᵗ-wt :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}
      {p : Up} →
    (σ : Substᵗ) →
    Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    substStoreᵗ σ Σ ∣ Φ ⊢ subst⊑ᵗ σ p ⦂ substᵗ σ A ⊑ substᵗ σ B
  ⊑-substᵗ-wt σ (wt-；tag ⊢p g ok) =
    wt-；tag (⊑-substᵗ-wt σ ⊢p) (substᵗ-ground σ g) (substᵗ-ground-ok σ g ok)
  ⊑-substᵗ-wt σ (wt-unseal； h α∈ ⊢p) =
    wt-unseal； (substLookupᵗ σ h) α∈ (⊑-substᵗ-wt σ ⊢p)
  ⊑-substᵗ-wt σ (wt-unseal★； h α∈ ⊢p) =
    wt-unseal★； (substLookupᵗ σ h) α∈ (⊑-substᵗ-wt σ ⊢p)
  ⊑-substᵗ-wt σ (wt-↦ ⊢p ⊢q) = wt-↦ (⊒-substᵗ-wt σ ⊢p) (⊑-substᵗ-wt σ ⊢q)
  ⊑-substᵗ-wt {Σ = Σ} σ (wt-∀ ⊢p) =
    wt-∀
      (castWt⊑
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        (⊑-substᵗ-wt (extsᵗ σ) ⊢p))
  ⊑-substᵗ-wt {Σ = Σ} σ (wt-ν {A = A} {B = B} ⊢p) =
    wt-ν
      (castWt⊑
        (substStoreᵗ-cons-⟰ˢ σ ★ Σ)
        refl
        (castWt⊑-raw
          (substᵗ-ν-src σ A)
          (substᵗ-⇑ˢ σ B)
          (⊑-substᵗ-wt (liftSubstˢ σ) ⊢p)))
  ⊑-substᵗ-wt σ (wt-id {A = A} wfA) = wt-id (wfTySome (substᵗ σ A))

  ⊒-substᵗ-wt :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}
      {p : Down} →
    (σ : Substᵗ) →
    Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    substStoreᵗ σ Σ ∣ Φ ⊢ subst⊒ᵗ σ p ⦂ substᵗ σ A ⊒ substᵗ σ B
  ⊒-substᵗ-wt σ (wt-untag； g ok ℓ ⊢p) =
    wt-untag； (substᵗ-ground σ g) (substᵗ-ground-ok σ g ok) ℓ (⊒-substᵗ-wt σ ⊢p)
  ⊒-substᵗ-wt σ (wt-；seal ⊢p h α∈) =
    wt-；seal (⊒-substᵗ-wt σ ⊢p) (substLookupᵗ σ h) α∈
  ⊒-substᵗ-wt σ (wt-；seal★ ⊢p h α∈) =
    wt-；seal★ (⊒-substᵗ-wt σ ⊢p) (substLookupᵗ σ h) α∈
  ⊒-substᵗ-wt σ (wt-↦ ⊢p ⊢q) = wt-↦ (⊑-substᵗ-wt σ ⊢p) (⊒-substᵗ-wt σ ⊢q)
  ⊒-substᵗ-wt {Σ = Σ} σ (wt-∀ ⊢p) =
    wt-∀
      (castWt⊒
        (substStoreᵗ-ext-⟰ᵗ σ Σ)
        refl
        (⊒-substᵗ-wt (extsᵗ σ) ⊢p))
  ⊒-substᵗ-wt {Σ = Σ} σ (wt-ν {A = A} {B = B} ⊢p) =
    wt-ν
      (castWt⊒
        (substStoreᵗ-cons-⟰ˢ σ ★ Σ)
        refl
        (castWt⊒-raw
          (substᵗ-⇑ˢ σ B)
          (substᵗ-ν-src σ A)
          (⊒-substᵗ-wt (liftSubstˢ σ) ⊢p)))
  ⊒-substᵗ-wt σ (wt-id {A = A} wfA) = wt-id (wfTySome (substᵗ σ A))

[]⊑ᵗ-wt :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}
    {p : Up}
  → Σ ∣ Φ ⊢ p ⦂ A ⊑ B
  → (T : Ty)
  → substStoreᵗ (singleTyEnv T) Σ ∣ Φ ⊢ p [ T ]⊑ ⦂ (A [ T ]ᵗ) ⊑ (B [ T ]ᵗ)
[]⊑ᵗ-wt h T = ⊑-substᵗ-wt (singleTyEnv T) h

[]⊒ᵗ-wt :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}
    {p : Down}
  → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
  → (T : Ty)
  → substStoreᵗ (singleTyEnv T) Σ ∣ Φ ⊢ p [ T ]⊒ ⦂ (A [ T ]ᵗ) ⊒ (B [ T ]ᵗ)
[]⊒ᵗ-wt h T = ⊒-substᵗ-wt (singleTyEnv T) h

inst-∀ν-⊑ :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Up}
  → ⟰ᵗ Σ ∣ Φ ⊢ p ⦂ A ⊑ B
  → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ ((↑⊑ˢ p) [ α₀ ]⊑) ⦂ (⇑ˢ A) [ α₀ ]ᵗ ⊑ (⇑ˢ B) [ α₀ ]ᵗ
inst-∀ν-⊑ {Σ} {Φ} {A} {B} {p} ⊢p =
  castWt⊑ store-eq refl ([]⊑ᵗ-wt weakened α₀)
  where
    okΦ : RenOk suc Φ (cast-seal ∷ Φ)
    okΦ p = there p

    okConv : RenOkConv suc Φ (cast-seal ∷ Φ)
    okConv p = there-conv p

    okCast : RenOkCast suc Φ (cast-seal ∷ Φ)
    okCast p = there-cast p

    okTag : RenOkTag suc Φ (cast-seal ∷ Φ)
    okTag p = there-tag p

    ok¬Φ : RenNotIn suc Φ (cast-seal ∷ Φ)
    ok¬Φ α∉Φ (there p) = α∉Φ p

    renamed :
      renameStoreˢ suc (⟰ᵗ Σ) ∣ (cast-seal ∷ Φ) ⊢ ↑⊑ˢ p ⦂ ⇑ˢ A ⊑ ⇑ˢ B
    renamed = ⊑-renameˢ-wt suc okΦ okConv okCast okTag ok¬Φ ⊢p

    weakened :
      ((zero , ★) ∷ renameStoreˢ suc (⟰ᵗ Σ)) ∣ (cast-seal ∷ Φ) ⊢ ↑⊑ˢ p ⦂ ⇑ˢ A ⊑ ⇑ˢ B
    weakened = wk⊑ (drop ⊆ˢ-refl) renamed

    store-tail :
      substStoreᵗ (singleTyEnv α₀) (renameStoreˢ suc (⟰ᵗ Σ)) ≡ ⟰ˢ Σ
    store-tail =
      trans
        (cong (substStoreᵗ (singleTyEnv α₀)) (renameStoreˢ-ext-⟰ᵗ suc Σ))
        (substStoreᵗ-singleTyEnv-⟰ᵗ α₀ (renameStoreˢ suc Σ))

    store-eq :
      substStoreᵗ (singleTyEnv α₀) ((zero , ★) ∷ renameStoreˢ suc (⟰ᵗ Σ)) ≡
      ((zero , ★) ∷ ⟰ˢ Σ)
    store-eq = cong₂ _∷_ refl store-tail

inst-∀ν-⊒ :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down}
  → ⟰ᵗ Σ ∣ Φ ⊢ p ⦂ A ⊒ B
  → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ((↑⊒ˢ p) [ α₀ ]⊒) ⦂ (⇑ˢ A) [ α₀ ]ᵗ ⊒ (⇑ˢ B) [ α₀ ]ᵗ
inst-∀ν-⊒ {Σ} {Φ} {A} {B} {p} ⊢p =
  castWt⊒ store-eq refl ([]⊒ᵗ-wt weakened α₀)
  where
    okΦ : RenOk suc Φ (cast-tag ∷ Φ)
    okΦ p = there p

    okConv : RenOkConv suc Φ (cast-tag ∷ Φ)
    okConv p = there-conv p

    okCast : RenOkCast suc Φ (cast-tag ∷ Φ)
    okCast p = there-cast p

    okTag : RenOkTag suc Φ (cast-tag ∷ Φ)
    okTag p = there-tag p

    ok¬Φ : RenNotIn suc Φ (cast-tag ∷ Φ)
    ok¬Φ α∉Φ (there p) = α∉Φ p

    renamed :
      renameStoreˢ suc (⟰ᵗ Σ) ∣ (cast-tag ∷ Φ) ⊢ ↑⊒ˢ p ⦂ ⇑ˢ A ⊒ ⇑ˢ B
    renamed = ⊒-renameˢ-wt suc okΦ okConv okCast okTag ok¬Φ ⊢p

    weakened :
      ((zero , ⇑ˢ ★) ∷ renameStoreˢ suc (⟰ᵗ Σ)) ∣ (cast-tag ∷ Φ) ⊢ ↑⊒ˢ p ⦂ ⇑ˢ A ⊒ ⇑ˢ B
    weakened = wk⊒ (drop ⊆ˢ-refl) renamed

    store-tail :
      substStoreᵗ (singleTyEnv α₀) (renameStoreˢ suc (⟰ᵗ Σ)) ≡ ⟰ˢ Σ
    store-tail =
      trans
        (cong (substStoreᵗ (singleTyEnv α₀)) (renameStoreˢ-ext-⟰ᵗ suc Σ))
        (substStoreᵗ-singleTyEnv-⟰ᵗ α₀ (renameStoreˢ suc Σ))

    store-eq :
      substStoreᵗ (singleTyEnv α₀) ((zero , ⇑ˢ ★) ∷ renameStoreˢ suc (⟰ᵗ Σ)) ≡
      ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ)
    store-eq = cong₂ _∷_ refl store-tail

lift-ν-arg-⊑ :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}{q : Up}
  → Σ ∣ Φ ⊢ q ⦂ A ⊑ B
  → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ ↑⊑ˢ q ⦂ ⇑ˢ A ⊑ ⇑ˢ B
lift-ν-arg-⊑ {Σ} {Φ} {A} {B} {q} ⊢q = wk⊑ (drop ⊆ˢ-refl) renamed
  where
    okΦ : RenOk suc Φ (cast-seal ∷ Φ)
    okΦ p = there p

    okConv : RenOkConv suc Φ (cast-seal ∷ Φ)
    okConv p = there-conv p

    okCast : RenOkCast suc Φ (cast-seal ∷ Φ)
    okCast p = there-cast p

    okTag : RenOkTag suc Φ (cast-seal ∷ Φ)
    okTag p = there-tag p

    ok¬Φ : RenNotIn suc Φ (cast-seal ∷ Φ)
    ok¬Φ α∉Φ (there p) = α∉Φ p

    renamed : renameStoreˢ suc Σ ∣ (cast-seal ∷ Φ) ⊢ ↑⊑ˢ q ⦂ ⇑ˢ A ⊑ ⇑ˢ B
    renamed = ⊑-renameˢ-wt suc okΦ okConv okCast okTag ok¬Φ ⊢q

lift-ν-arg-⊒ :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down}
  → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
  → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ↑⊒ˢ p ⦂ ⇑ˢ A ⊒ ⇑ˢ B
lift-ν-arg-⊒ {Σ} {Φ} {A} {B} {p} ⊢p = wk⊒ (drop ⊆ˢ-refl) renamed
  where
    okΦ : RenOk suc Φ (cast-tag ∷ Φ)
    okΦ p = there p

    okConv : RenOkConv suc Φ (cast-tag ∷ Φ)
    okConv p = there-conv p

    okCast : RenOkCast suc Φ (cast-tag ∷ Φ)
    okCast p = there-cast p

    okTag : RenOkTag suc Φ (cast-tag ∷ Φ)
    okTag p = there-tag p

    ok¬Φ : RenNotIn suc Φ (cast-tag ∷ Φ)
    ok¬Φ α∉Φ (there p) = α∉Φ p

    renamed : renameStoreˢ suc Σ ∣ (cast-tag ∷ Φ) ⊢ ↑⊒ˢ p ⦂ ⇑ˢ A ⊒ ⇑ˢ B
    renamed = ⊒-renameˢ-wt suc okΦ okConv okCast okTag ok¬Φ ⊢p

mutual
  ⨟↑-fuel : ℕ → Up → Up → Up
  ⨟↑-fuel zero p q = p
  ⨟↑-fuel (suc n) p (q ；tag G) = (⨟↑-fuel n p q) ；tag G
  ⨟↑-fuel (suc n) (unseal α ； p) q = unseal α ； (⨟↑-fuel n p q)
  ⨟↑-fuel (suc n) (p ↦ q) (r ↦ s) = (⨟↓-fuel n r p) ↦ (⨟↑-fuel n q s)
  ⨟↑-fuel (suc n) (∀ᵖ p) (∀ᵖ q) = ∀ᵖ (⨟↑-fuel n p q)
  ⨟↑-fuel (suc n) (∀ᵖ p) (ν q) = ν (⨟↑-fuel n ((↑⊑ˢ p) [ α₀ ]⊑) q)
  ⨟↑-fuel (suc n) (ν p) q = ν (⨟↑-fuel n p (↑⊑ˢ q))
  ⨟↑-fuel (suc n) (id A) q = q
  ⨟↑-fuel (suc n) p (id A) = p
  ⨟↑-fuel (suc n) p q = p

  ⨟↓-fuel : ℕ → Down → Down → Down
  ⨟↓-fuel zero p q = p
  ⨟↓-fuel (suc n) p (q ；seal α) = (⨟↓-fuel n p q) ；seal α
  ⨟↓-fuel (suc n) (untag G [ ℓ ]； p) q = untag G [ ℓ ]； (⨟↓-fuel n p q)
  ⨟↓-fuel (suc n) (p ↦ q) (r ↦ s) = (⨟↑-fuel n r p) ↦ (⨟↓-fuel n q s)
  ⨟↓-fuel (suc n) (∀ᵖ p) (∀ᵖ q) = ∀ᵖ (⨟↓-fuel n p q)
  ⨟↓-fuel (suc n) (ν p) (∀ᵖ q) = ν (⨟↓-fuel n p ((↑⊒ˢ q) [ α₀ ]⊒))
  ⨟↓-fuel (suc n) p (ν q) = ν (⨟↓-fuel n (↑⊒ˢ p) q)
  ⨟↓-fuel (suc n) (id A) q = q
  ⨟↓-fuel (suc n) p (id A) = p
  ⨟↓-fuel (suc n) p q = p

mutual
  _⨟↑_ : Up → Up → Up
  p ⨟↑ q = ⨟↑-fuel (suc (size↑ p + size↑ q)) p q

  _⨟↓_ : Down → Down → Down
  p ⨟↓ q = ⨟↓-fuel (suc (size↓ p + size↓ q)) p q

mutual
  wt-⨟↑-fuel :
    ∀ {n : ℕ}{Σ : Store}{Φ : List CastPerm}{A B C : Ty}{p : Up}{q : Up}
    → suc (size↑ p + size↑ q) ≤ n
    → Σ ∣ Φ ⊢ p ⦂ A ⊑ B
    → Σ ∣ Φ ⊢ q ⦂ B ⊑ C
    → Σ ∣ Φ ⊢ ⨟↑-fuel n p q ⦂ A ⊑ C
  wt-⨟↑-fuel {n = zero} ()
  wt-⨟↑-fuel {n = suc n} hle (wt-id wfA) (wt-；tag ⊢q g ok) =
    wt-；tag (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) (wt-id wfA) ⊢q) g ok
  wt-⨟↑-fuel {n = suc n} hle (wt-id wfA) (wt-unseal； h α∈ ⊢q) = wt-unseal； h α∈ ⊢q
  wt-⨟↑-fuel {n = suc n} hle (wt-id wfA) (wt-unseal★； h α∈ ⊢q) = wt-unseal★； h α∈ ⊢q
  wt-⨟↑-fuel {n = suc n} hle (wt-id wfA) (wt-↦ ⊢q₁ ⊢q₂) = wt-↦ ⊢q₁ ⊢q₂
  wt-⨟↑-fuel {n = suc n} hle (wt-id wfA) (wt-∀ ⊢q) = wt-∀ ⊢q
  wt-⨟↑-fuel {n = suc n} hle (wt-id wfA) (wt-ν ⊢q) = wt-ν ⊢q
  wt-⨟↑-fuel {n = suc n} hle (wt-id wfA) (wt-id wfC) = wt-id wfA
  wt-⨟↑-fuel {n = suc n} hle (wt-；tag ⊢p g ok) (wt-id wfC) = wt-；tag ⊢p g ok
  wt-⨟↑-fuel {n = suc n} hle (wt-unseal； h α∈ ⊢p) (wt-id wfC) =
    wt-unseal； h α∈ (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p (wt-id wfC))
  wt-⨟↑-fuel {n = suc n} hle (wt-unseal★； h α∈ ⊢p) (wt-id wfC) =
    wt-unseal★； h α∈ (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p (wt-id wfC))
  wt-⨟↑-fuel {n = suc n} hle (wt-↦ ⊢p₁ ⊢p₂) (wt-id wfC) = wt-↦ ⊢p₁ ⊢p₂
  wt-⨟↑-fuel {n = suc n} hle (wt-∀ ⊢p) (wt-id wfC) = wt-∀ ⊢p
  wt-⨟↑-fuel {n = suc n} hle (wt-ν {B = B} ⊢p) (wt-id wfC) =
    wt-ν (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p (wt-id (wfTySome (⇑ˢ B))))
  wt-⨟↑-fuel {n = suc n} {p = p} {q = q ；tag G} hle ⊢p (wt-；tag ⊢q g ok) =
    wt-；tag (wt-⨟↑-fuel {n = n} (pred-tag-bound↑ {p = p} {q = q} {G = G} hle) ⊢p ⊢q) g ok
  wt-⨟↑-fuel {n = suc n} hle (wt-unseal； h α∈ ⊢p) ⊢q@(wt-unseal； hq β∈ ⊢q₀) =
    wt-unseal； h α∈ (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↑-fuel {n = suc n} hle (wt-unseal； h α∈ ⊢p) ⊢q@(wt-unseal★； hq β∈ ⊢q₀) =
    wt-unseal； h α∈ (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↑-fuel {n = suc n} hle (wt-unseal； h α∈ ⊢p) ⊢q@(wt-↦ ⊢q₁ ⊢q₂) =
    wt-unseal； h α∈ (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↑-fuel {n = suc n} hle (wt-unseal； h α∈ ⊢p) ⊢q@(wt-∀ ⊢q₀) =
    wt-unseal； h α∈ (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↑-fuel {n = suc n} hle (wt-unseal； h α∈ ⊢p) ⊢q@(wt-ν ⊢q₀) =
    wt-unseal； h α∈ (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↑-fuel {n = suc n} hle (wt-unseal★； h α∈ ⊢p) ⊢q@(wt-unseal； hq β∈ ⊢q₀) =
    wt-unseal★； h α∈ (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↑-fuel {n = suc n} hle (wt-unseal★； h α∈ ⊢p) ⊢q@(wt-unseal★； hq β∈ ⊢q₀) =
    wt-unseal★； h α∈ (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↑-fuel {n = suc n} hle (wt-unseal★； h α∈ ⊢p) ⊢q@(wt-↦ ⊢q₁ ⊢q₂) =
    wt-unseal★； h α∈ (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↑-fuel {n = suc n} hle (wt-unseal★； h α∈ ⊢p) ⊢q@(wt-∀ ⊢q₀) =
    wt-unseal★； h α∈ (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↑-fuel {n = suc n} hle (wt-unseal★； h α∈ ⊢p) ⊢q@(wt-ν ⊢q₀) =
    wt-unseal★； h α∈ (wt-⨟↑-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↑-fuel {n = suc n} {p = p↓ ↦ p↑} {q = q↓ ↦ q↑} hle (wt-↦ ⊢p₁ ⊢p₂) (wt-↦ ⊢q₁ ⊢q₂) =
    wt-↦
      (wt-⨟↓-fuel {n = n} (pred-↦-bound-left {a = size↓ p↓} {b = size↑ p↑} {c = size↓ q↓} {d = size↑ q↑} hle) ⊢q₁ ⊢p₁)
      (wt-⨟↑-fuel {n = n} (pred-↦-bound-right {a = size↓ p↓} {b = size↑ p↑} {c = size↓ q↓} {d = size↑ q↑} hle) ⊢p₂ ⊢q₂)
  wt-⨟↑-fuel {n = suc n} hle (wt-∀ ⊢p) (wt-∀ ⊢q) =
    wt-∀ (wt-⨟↑-fuel {n = n} (pred-∀-bound↑ hle) ⊢p ⊢q)
  wt-⨟↑-fuel {n = suc n} hle (wt-∀ ⊢p) (wt-ν ⊢q) =
    wt-ν (wt-⨟↑-fuel {n = n} (pred-∀ν-bound↑ hle) (inst-∀ν-⊑ ⊢p) ⊢q)
  wt-⨟↑-fuel {n = suc n} {p = ν p} {q = unseal α ； q}
    hle (wt-ν ⊢p) ⊢q@(wt-unseal； h α∈ ⊢q₀) =
    wt-ν (wt-⨟↑-fuel {n = n} (pred-ν-bound↑ {p = p} {q = unseal α ； q} hle) ⊢p (lift-ν-arg-⊑ ⊢q))
  wt-⨟↑-fuel {n = suc n} {p = ν p} {q = unseal α ； q}
    hle (wt-ν ⊢p) ⊢q@(wt-unseal★； h α∈ ⊢q₀) =
    wt-ν (wt-⨟↑-fuel {n = n} (pred-ν-bound↑ {p = p} {q = unseal α ； q} hle) ⊢p (lift-ν-arg-⊑ ⊢q))
  wt-⨟↑-fuel {n = suc n} {p = ν p} {q = q↓ ↦ q↑}
    hle (wt-ν ⊢p) ⊢q@(wt-↦ ⊢q₁ ⊢q₂) =
    wt-ν (wt-⨟↑-fuel {n = n} (pred-ν-bound↑ {p = p} {q = q↓ ↦ q↑} hle) ⊢p (lift-ν-arg-⊑ ⊢q))
  wt-⨟↑-fuel {n = suc n} {p = ν p} {q = ∀ᵖ q}
    hle (wt-ν ⊢p) ⊢q@(wt-∀ ⊢q₀) =
    wt-ν (wt-⨟↑-fuel {n = n} (pred-ν-bound↑ {p = p} {q = ∀ᵖ q} hle) ⊢p (lift-ν-arg-⊑ ⊢q))
  wt-⨟↑-fuel {n = suc n} {p = ν p} {q = ν q}
    hle (wt-ν ⊢p) ⊢q@(wt-ν ⊢q₀) =
    wt-ν (wt-⨟↑-fuel {n = n} (pred-ν-bound↑ {p = p} {q = ν q} hle) ⊢p (lift-ν-arg-⊑ ⊢q))

  wt-⨟↓-fuel :
    ∀ {n : ℕ}{Σ : Store}{Φ : List CastPerm}{A B C : Ty}{p : Down}{q : Down}
    → suc (size↓ p + size↓ q) ≤ n
    → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
    → Σ ∣ Φ ⊢ q ⦂ B ⊒ C
    → Σ ∣ Φ ⊢ ⨟↓-fuel n p q ⦂ A ⊒ C
  wt-⨟↓-fuel {n = zero} ()
  wt-⨟↓-fuel {n = suc n} {p = id A} {q = q ；seal α} hle (wt-id wfA) (wt-；seal ⊢q h α∈) =
    wt-；seal (wt-⨟↓-fuel {n = n} (pred-seal-bound↓ {p = id A} {q = q} {α = α} hle) (wt-id wfA) ⊢q) h α∈
  wt-⨟↓-fuel {n = suc n} {p = id A} {q = q ；seal α} hle (wt-id wfA) (wt-；seal★ ⊢q h α∈) =
    wt-；seal★ (wt-⨟↓-fuel {n = n} (pred-seal-bound↓ {p = id A} {q = q} {α = α} hle) (wt-id wfA) ⊢q) h α∈
  wt-⨟↓-fuel {n = suc n} hle (wt-id wfA) (wt-untag； g ok ℓ ⊢q) = wt-untag； g ok ℓ ⊢q
  wt-⨟↓-fuel {n = suc n} hle (wt-id wfA) (wt-↦ ⊢q₁ ⊢q₂) = wt-↦ ⊢q₁ ⊢q₂
  wt-⨟↓-fuel {n = suc n} hle (wt-id wfA) (wt-∀ ⊢q) = wt-∀ ⊢q
  wt-⨟↓-fuel {n = suc n} hle (wt-id {A = A} wfA) (wt-ν ⊢q) =
    wt-ν (wt-⨟↓-fuel {n = n} (s≤s⁻¹ hle) (wt-id (wfTySome (⇑ˢ A))) ⊢q)
  wt-⨟↓-fuel {n = suc n} hle (wt-id wfA) (wt-id wfC) = wt-id wfA
  wt-⨟↓-fuel {n = suc n} hle (wt-untag； g ok ℓ ⊢p) (wt-id wfC) =
    wt-untag； g ok ℓ (wt-⨟↓-fuel {n = n} (s≤s⁻¹ hle) ⊢p (wt-id wfC))
  wt-⨟↓-fuel {n = suc n} hle (wt-；seal ⊢p h α∈) (wt-id wfC) = wt-；seal ⊢p h α∈
  wt-⨟↓-fuel {n = suc n} hle (wt-；seal★ ⊢p h α∈) (wt-id wfC) = wt-；seal★ ⊢p h α∈
  wt-⨟↓-fuel {n = suc n} hle (wt-↦ ⊢p₁ ⊢p₂) (wt-id wfC) = wt-↦ ⊢p₁ ⊢p₂
  wt-⨟↓-fuel {n = suc n} hle (wt-∀ ⊢p) (wt-id wfC) = wt-∀ ⊢p
  wt-⨟↓-fuel {n = suc n} hle (wt-ν ⊢p) (wt-id wfC) = wt-ν ⊢p
  wt-⨟↓-fuel {n = suc n} {p = p} {q = q ；seal α} hle ⊢p (wt-；seal ⊢q h α∈) =
    wt-；seal (wt-⨟↓-fuel {n = n} (pred-seal-bound↓ {p = p} {q = q} {α = α} hle) ⊢p ⊢q) h α∈
  wt-⨟↓-fuel {n = suc n} {p = p} {q = q ；seal α} hle ⊢p (wt-；seal★ ⊢q h α∈) =
    wt-；seal★ (wt-⨟↓-fuel {n = n} (pred-seal-bound↓ {p = p} {q = q} {α = α} hle) ⊢p ⊢q) h α∈
  wt-⨟↓-fuel {n = suc n} {p = untag G [ ℓ ]； p} hle (wt-untag； g ok ℓ′ ⊢p) ⊢q@(wt-untag； gq okq ℓq ⊢q₀) =
    wt-untag； g ok ℓ′ (wt-⨟↓-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↓-fuel {n = suc n} {p = untag G [ ℓ ]； p} hle (wt-untag； g ok ℓ′ ⊢p) ⊢q@(wt-↦ ⊢q₁ ⊢q₂) =
    wt-untag； g ok ℓ′ (wt-⨟↓-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↓-fuel {n = suc n} {p = untag G [ ℓ ]； p} hle (wt-untag； g ok ℓ′ ⊢p) ⊢q@(wt-∀ ⊢q₀) =
    wt-untag； g ok ℓ′ (wt-⨟↓-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↓-fuel {n = suc n} {p = untag G [ ℓ ]； p} hle (wt-untag； g ok ℓ′ ⊢p) ⊢q@(wt-ν ⊢q₀) =
    wt-untag； g ok ℓ′ (wt-⨟↓-fuel {n = n} (s≤s⁻¹ hle) ⊢p ⊢q)
  wt-⨟↓-fuel {n = suc n} {p = p↑ ↦ p↓} {q = q↑ ↦ q↓} hle (wt-↦ ⊢p₁ ⊢p₂) (wt-↦ ⊢q₁ ⊢q₂) =
    wt-↦
      (wt-⨟↑-fuel {n = n} (pred-↦-bound-left {a = size↑ p↑} {b = size↓ p↓} {c = size↑ q↑} {d = size↓ q↓} hle) ⊢q₁ ⊢p₁)
      (wt-⨟↓-fuel {n = n} (pred-↦-bound-right {a = size↑ p↑} {b = size↓ p↓} {c = size↑ q↑} {d = size↓ q↓} hle) ⊢p₂ ⊢q₂)
  wt-⨟↓-fuel {n = suc n} hle (wt-∀ ⊢p) (wt-∀ ⊢q) =
    wt-∀ (wt-⨟↓-fuel {n = n} (pred-∀-bound↓ hle) ⊢p ⊢q)
  wt-⨟↓-fuel {n = suc n} hle (wt-ν ⊢p) (wt-∀ ⊢q) =
    wt-ν (wt-⨟↓-fuel {n = n} (pred-ν∀-bound↓ hle) ⊢p (inst-∀ν-⊒ ⊢q))
  wt-⨟↓-fuel {n = suc n} {p = p ；seal α} {q = ν q}
    hle ⊢p@(wt-；seal ⊢p₀ h α∈) (wt-ν ⊢q) =
    wt-ν (wt-⨟↓-fuel {n = n} (pred-ν-bound↓ {p = p ；seal α} {q = q} hle) (lift-ν-arg-⊒ ⊢p) ⊢q)
  wt-⨟↓-fuel {n = suc n} {p = p ；seal α} {q = ν q}
    hle ⊢p@(wt-；seal★ ⊢p₀ h α∈) (wt-ν ⊢q) =
    wt-ν (wt-⨟↓-fuel {n = n} (pred-ν-bound↓ {p = p ；seal α} {q = q} hle) (lift-ν-arg-⊒ ⊢p) ⊢q)
  wt-⨟↓-fuel {n = suc n} {p = p↑ ↦ p↓} {q = ν q}
    hle ⊢p@(wt-↦ ⊢p₁ ⊢p₂) (wt-ν ⊢q) =
    wt-ν (wt-⨟↓-fuel {n = n} (pred-ν-bound↓ {p = p↑ ↦ p↓} {q = q} hle) (lift-ν-arg-⊒ ⊢p) ⊢q)
  wt-⨟↓-fuel {n = suc n} {p = ∀ᵖ p} {q = ν q}
    hle ⊢p@(wt-∀ ⊢p₀) (wt-ν ⊢q) =
    wt-ν (wt-⨟↓-fuel {n = n} (pred-ν-bound↓ {p = ∀ᵖ p} {q = q} hle) (lift-ν-arg-⊒ ⊢p) ⊢q)
  wt-⨟↓-fuel {n = suc n} {p = ν p} {q = ν q}
    hle ⊢p@(wt-ν ⊢p₀) (wt-ν ⊢q) =
    wt-ν (wt-⨟↓-fuel {n = n} (pred-ν-bound↓ {p = ν p} {q = q} hle) (lift-ν-arg-⊒ ⊢p) ⊢q)

  wt-⨟↑ :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}{p : Up}{q : Up}
    → Σ ∣ Φ ⊢ p ⦂ A ⊑ B
    → Σ ∣ Φ ⊢ q ⦂ B ⊑ C
    → Σ ∣ Φ ⊢ p ⨟↑ q ⦂ A ⊑ C
  wt-⨟↑ {p = p} {q = q} ⊢p ⊢q = wt-⨟↑-fuel ≤-refl ⊢p ⊢q

  wt-⨟↓ :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}{p : Down}{q : Down}
    → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
    → Σ ∣ Φ ⊢ q ⦂ B ⊒ C
    → Σ ∣ Φ ⊢ p ⨟↓ q ⦂ A ⊒ C
  wt-⨟↓ {p = p} {q = q} ⊢p ⊢q = wt-⨟↓-fuel ≤-refl ⊢p ⊢q
