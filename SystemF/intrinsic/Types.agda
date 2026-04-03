{-# OPTIONS --rewriting #-}

module Types where

-- Need the following two imports for rewriting
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      ---------------------------
    → f ≡ g

infixr 7 _⇒_
infixr 6 _•ᵗ_

infix  9 `_

infixl 5 _,α
infixr 7 _⇒ʳ_
infixr 7 _⇒ˢ_
infixr 5 _⨟ᵗ_

---------------------------------------------------
-- | Type variable contexts and type variables | --
---------------------------------------------------

data TyCtx : Set where
  ∅    : TyCtx
  _,α  : TyCtx → TyCtx

data TyVar : (Δ : TyCtx) → Set where
  Z  : ∀ {Δ} → TyVar (Δ ,α)
  S_ : ∀ {Δ} → TyVar Δ → TyVar (Δ ,α)

---------------
-- | Types | --
---------------

data Type : TyCtx → Set where
  `_     : ∀ {Δ} → TyVar Δ → Type Δ
  `Nat   : ∀ {Δ} → Type Δ
  `Bool  : ∀ {Δ} → Type Δ
  _⇒_   : ∀ {Δ} → Type Δ → Type Δ → Type Δ
  `∀_    : ∀ {Δ} → Type (Δ ,α) → Type Δ

------------------------------------
-- | Substitute types into type | --
------------------------------------

_⇒ʳ_ : TyCtx → TyCtx → Set
Δ ⇒ʳ Δ' = TyVar Δ → TyVar Δ'

extᵗ : ∀ {Δ Δ'} → Δ ⇒ʳ Δ' → (Δ ,α) ⇒ʳ (Δ' ,α)
extᵗ ρ Z      = Z
extᵗ ρ (S x)  = S (ρ x)

renameᵗ : ∀ {Δ Δ'} → Δ ⇒ʳ Δ' → Type Δ → Type Δ'
renameᵗ ρ (` x)   = ` (ρ x)
renameᵗ ρ `Nat     = `Nat
renameᵗ ρ `Bool    = `Bool
renameᵗ ρ (A ⇒ B)  = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A)  = `∀ (renameᵗ (extᵗ ρ) A)

renameᵗ-cong : ∀ {Δ Δ'} {ρ ρ' : Δ ⇒ʳ Δ'} (A : Type Δ)
  → (∀ α → ρ α ≡ ρ' α)
    ---------------------------------
  → renameᵗ ρ A ≡ renameᵗ ρ' A
renameᵗ-cong (` α) eq = cong `_ (eq α)
renameᵗ-cong `Nat _ = refl
renameᵗ-cong `Bool _ = refl
renameᵗ-cong (A ⇒ B) eq rewrite renameᵗ-cong A eq | renameᵗ-cong B eq = refl
renameᵗ-cong {ρ = ρ} {ρ'} (`∀ A) eq = cong `∀_ (renameᵗ-cong A ext-eq)
  where
  ext-eq : ∀ α → extᵗ ρ α ≡ extᵗ ρ' α
  ext-eq Z      = refl
  ext-eq (S α)  = cong S_ (eq α)

renameᵗ-comp : ∀ {Δ₁ Δ₂ Δ₃} (ρ₁ : Δ₁ ⇒ʳ Δ₂) (ρ₂ : Δ₂ ⇒ʳ Δ₃) A
    ---------------------------------------------------------------
  → renameᵗ ρ₂ (renameᵗ ρ₁ A) ≡ renameᵗ (λ α → ρ₂ (ρ₁ α)) A
renameᵗ-comp ρ₁ ρ₂ (` α)  = refl
renameᵗ-comp ρ₁ ρ₂ `Nat   = refl
renameᵗ-comp ρ₁ ρ₂ `Bool  = refl
renameᵗ-comp ρ₁ ρ₂ (A ⇒ B)
  rewrite renameᵗ-comp ρ₁ ρ₂ A | renameᵗ-comp ρ₁ ρ₂ B = refl
renameᵗ-comp ρ₁ ρ₂ (`∀ A) = cong `∀_
    (trans (renameᵗ-comp (extᵗ ρ₁) (extᵗ ρ₂) A)
           (renameᵗ-cong A ext-comp))
  where
  ext-comp : ∀ α → extᵗ ρ₂ (extᵗ ρ₁ α) ≡ extᵗ (λ β → ρ₂ (ρ₁ β)) α
  ext-comp Z      = refl
  ext-comp (S α)  = refl

⇑ᵗ : ∀ {Δ} (A : Type Δ) → Type (Δ ,α)
⇑ᵗ = renameᵗ S_

-- check
renameᵗ-shift : ∀ {Δ Ξ} (ρ : Δ ⇒ʳ Ξ) A → renameᵗ (extᵗ ρ) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ ρ A)
renameᵗ-shift ρ A =
  trans
    (renameᵗ-comp S_ (extᵗ ρ) A)
    (trans
      (renameᵗ-cong A (λ α → refl))
      (sym (renameᵗ-comp ρ S_ A)))

_⇒ˢ_ : TyCtx → TyCtx → Set
Δ ⇒ˢ Δ' = TyVar Δ → Type Δ'

idᵗ : ∀ {Δ} → Δ ⇒ˢ Δ
idᵗ = `_

↑ᵗ : ∀ {Δ} → Δ ⇒ˢ (Δ ,α)
↑ᵗ α = ` (S α)

extsᵗ : ∀ {Δ Δ'} → Δ ⇒ˢ Δ' → (Δ ,α) ⇒ˢ (Δ' ,α)
extsᵗ σ Z      = ` Z
extsᵗ σ (S x)  = ⇑ᵗ (σ x)

_•ᵗ_ : ∀ {Δ Δ'} → Type Δ' → Δ ⇒ˢ Δ' → (Δ ,α) ⇒ˢ Δ'
(A •ᵗ σ) Z      = A
(A •ᵗ σ) (S α)  = σ α

substᵗ : ∀ {Δ Δ'} → Δ ⇒ˢ Δ' → Type Δ → Type Δ'
substᵗ σ (` x)   = σ x
substᵗ σ `Nat     = `Nat
substᵗ σ `Bool    = `Bool
substᵗ σ (A ⇒ B)  = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (`∀ A)  = `∀ (substᵗ (extsᵗ σ) A)

_⨟ᵗ_ : ∀ {Δ₁ Δ₂ Δ₃} → Δ₁ ⇒ˢ Δ₂ → Δ₂ ⇒ˢ Δ₃ → Δ₁ ⇒ˢ Δ₃
(σ ⨟ᵗ τ) α = substᵗ τ (σ α)

σ₀ᵗ : ∀ {Δ} → Type Δ → (Δ ,α) ⇒ˢ Δ
σ₀ᵗ B = B •ᵗ idᵗ

_[_]ᵗ : ∀ {Δ} → Type (Δ ,α) → Type Δ → Type Δ
A [ B ]ᵗ = substᵗ (σ₀ᵗ B) A

substᵗ-cong : ∀ {Δ Δ'} {σ τ : Δ ⇒ˢ Δ'} A
  → (∀ α → σ α ≡ τ α)
    ------------------------------
  → substᵗ σ A ≡ substᵗ τ A
substᵗ-cong (` α) eq = eq α
substᵗ-cong `Nat _ = refl
substᵗ-cong `Bool _ = refl
substᵗ-cong (A ⇒ B) eq rewrite substᵗ-cong A eq | substᵗ-cong B eq = refl
substᵗ-cong {σ = σ} {τ} (`∀ A) eq = cong `∀_ (substᵗ-cong A exts-eq)
  where
  exts-eq : ∀ α → extsᵗ σ α ≡ extsᵗ τ α
  exts-eq Z      = refl
  exts-eq (S α)  = cong ⇑ᵗ (eq α)

extsᵗ-extᵗ : ∀ {Δ₁ Δ₂ Δ₃} (ρ : Δ₁ ⇒ʳ Δ₂) (σ : Δ₂ ⇒ˢ Δ₃) α
      ------------------------------------------------------------
    → extsᵗ σ (extᵗ ρ α) ≡ extsᵗ (λ β → σ (ρ β)) α
extsᵗ-extᵗ ρ σ Z      = refl
extsᵗ-extᵗ ρ σ (S _)  = refl

ren-subᵗ : ∀ {Δ₁ Δ₂ Δ₃} (ρ : Δ₁ ⇒ʳ Δ₂) (σ : Δ₂ ⇒ˢ Δ₃) A
      ---------------------------------------------------------------
    → substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ α → σ (ρ α)) A
ren-subᵗ ρ σ (` α)  = refl
ren-subᵗ ρ σ `Nat   = refl
ren-subᵗ ρ σ `Bool  = refl
ren-subᵗ ρ σ (A ⇒ B) rewrite ren-subᵗ ρ σ A | ren-subᵗ ρ σ B = refl
ren-subᵗ ρ σ (`∀ A) = cong `∀_
  (trans
    (ren-subᵗ (extᵗ ρ) (extsᵗ σ) A)
    (substᵗ-cong A (extsᵗ-extᵗ ρ σ)))

sub-idᵗ : ∀ {Δ} (A : Type Δ) → substᵗ idᵗ A ≡ A
sub-idᵗ (` x)    = refl
sub-idᵗ `Nat     = refl
sub-idᵗ `Bool    = refl
sub-idᵗ (A ⇒ B)  rewrite sub-idᵗ A | sub-idᵗ B = refl
sub-idᵗ (`∀ A) = cong `∀_ eq
    where
    exts-id : ∀ α → extsᵗ idᵗ α ≡ ` α
    exts-id Z      = refl
    exts-id (S _)  = refl
    eq : substᵗ (extsᵗ idᵗ) A ≡ A
    eq rewrite substᵗ-cong A exts-id | sub-idᵗ A = refl

σ₀ᵗ-extᵗ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') (B : Type Δ) (x : TyVar (Δ ,α))
    → renameᵗ ρ (σ₀ᵗ B x) ≡ σ₀ᵗ (renameᵗ ρ B) (extᵗ ρ x)
σ₀ᵗ-extᵗ ρ B Z      = refl
σ₀ᵗ-extᵗ ρ B (S x)  = refl

extᵗ-extsᵗ : ∀ {Δ₁ Δ₂ Δ₃} (ρ : Δ₂ ⇒ʳ Δ₃) (σ : Δ₁ ⇒ˢ Δ₂) α
      ------------------------------------------------------------------
    → renameᵗ (extᵗ ρ) (extsᵗ σ α) ≡ extsᵗ (λ β → renameᵗ ρ (σ β)) α
extᵗ-extsᵗ ρ σ Z     = refl
extᵗ-extsᵗ ρ σ (S α) = renameᵗ-shift ρ (σ α)

sub-renᵗ : ∀ {Δ₁ Δ₂ Δ₃} (ρ : Δ₂ ⇒ʳ Δ₃) (σ : Δ₁ ⇒ˢ Δ₂) A
      ---------------------------------------------------------------
    → renameᵗ ρ (substᵗ σ A) ≡ substᵗ (λ α → renameᵗ ρ (σ α)) A
sub-renᵗ ρ σ (` α)  = refl
sub-renᵗ ρ σ `Nat   = refl
sub-renᵗ ρ σ `Bool  = refl
sub-renᵗ ρ σ (A ⇒ B) rewrite sub-renᵗ ρ σ A | sub-renᵗ ρ σ B = refl
sub-renᵗ ρ σ (`∀ A) = cong `∀_
  (trans
    (sub-renᵗ (extᵗ ρ) (extsᵗ σ) A)
    (substᵗ-cong A (extᵗ-extsᵗ ρ σ)))

-- check
renameᵗ-[]ᵗ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') (A : Type (Δ ,α)) (B : Type Δ)
    → renameᵗ ρ (A [ B ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ renameᵗ ρ B ]ᵗ
renameᵗ-[]ᵗ ρ A B =
  trans
    (sub-renᵗ ρ (σ₀ᵗ B) A)
    (trans
      (substᵗ-cong A (σ₀ᵗ-extᵗ ρ B))
      (sym (ren-subᵗ (extᵗ ρ) (σ₀ᵗ (renameᵗ ρ B)) A)))

extsᵗ-substᵗ : ∀ {Δ₁ Δ₂ Δ₃} (σ : Δ₁ ⇒ˢ Δ₂) (τ : Δ₂ ⇒ˢ Δ₃) α
      ------------------------------------------------------------
    → substᵗ (extsᵗ τ) (extsᵗ σ α) ≡ extsᵗ (σ ⨟ᵗ τ) α
extsᵗ-substᵗ σ τ Z      = refl
extsᵗ-substᵗ σ τ (S x) =
  trans
    (ren-subᵗ S_ (extsᵗ τ) (σ x))
    (trans
      (substᵗ-cong (σ x) (λ α → refl))
      (sym (sub-renᵗ S_ τ (σ x))))

sub-subᵗ : ∀ {Δ₁ Δ₂ Δ₃} (σ : Δ₁ ⇒ˢ Δ₂) (τ : Δ₂ ⇒ˢ Δ₃) A
      ---------------------------------------------------------------
    → substᵗ τ (substᵗ σ A) ≡ substᵗ (σ ⨟ᵗ τ) A
sub-subᵗ σ τ (` α)   = refl
sub-subᵗ σ τ `Nat    = refl
sub-subᵗ σ τ `Bool   = refl
sub-subᵗ σ τ (A ⇒ B) rewrite sub-subᵗ σ τ A | sub-subᵗ σ τ B = refl
sub-subᵗ σ τ (`∀ A) = cong `∀_
  (trans
    (sub-subᵗ (extsᵗ σ) (extsᵗ τ) A)
    (substᵗ-cong A (extsᵗ-substᵗ σ τ)))

substᵗ-σ₀ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') (B : Type Δ) (x : TyVar (Δ ,α))
    → substᵗ σ (σ₀ᵗ B x) ≡ substᵗ (σ₀ᵗ (substᵗ σ B)) (extsᵗ σ x)
substᵗ-σ₀ σ B Z      = refl
substᵗ-σ₀ σ B (S x)  =
  trans
    (sym (sub-idᵗ (σ x)))
    (trans
      (sym (substᵗ-cong (σ x) (λ α → refl)))
      (sym (ren-subᵗ S_ (σ₀ᵗ (substᵗ σ B)) (σ x))))

substᵗ-[]ᵗ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') (A : Type (Δ ,α)) (B : Type Δ)
    → substᵗ σ (A [ B ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ substᵗ σ B ]ᵗ
substᵗ-[]ᵗ σ A B =
  trans
    (sub-subᵗ (σ₀ᵗ B) σ A)
    (trans
      (substᵗ-cong A (substᵗ-σ₀ σ B))
      (sym (sub-subᵗ (extsᵗ σ) (σ₀ᵗ (substᵗ σ B)) A)))

exts-sub-consᵗ : ∀ {Δ Δ'} (A : Type (Δ ,α)) (σ : Δ ⇒ˢ Δ') (B : Type Δ')
    → (substᵗ (extsᵗ σ) A) [ B ]ᵗ ≡ substᵗ (B •ᵗ σ) A
exts-sub-consᵗ A σ B =
  trans
    (sub-subᵗ (extsᵗ σ) (σ₀ᵗ B) A)
    (substᵗ-cong A eq)
    where
    eq : ∀ β → substᵗ (σ₀ᵗ B) (extsᵗ σ β) ≡ (B •ᵗ σ) β
    eq Z      = refl
    eq (S β)  =
      trans
        (ren-subᵗ S_ (σ₀ᵗ B) (σ β))
        (trans
          (substᵗ-cong (σ β) (λ α → refl))
          (sub-idᵗ (σ β)))
