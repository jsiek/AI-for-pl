module NuTerms where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax)

open import Types
open import Ctx
open import Coercions
open import Primitives

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_
infix  5 Λ_
infixl 7 _·_
infixl 7 _•_
infixl 7 _⟨_⟩
infixl 6 _⊕[_]_
infix  9 `_

data Term : Set where
  `_      : Var → Term
  ƛ_      : Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  _•_     : Term → TyVar → Term
  ν       : Ty → Term → Term
  $       : Const → Term
  _⊕[_]_  : Term → Prim → Term → Term
  _⟨_⟩    : Term → Coercion → Term
  blame   : Label → Term

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value : Term → Set where
  ƛ_ : (N : Term) → Value (ƛ N)
  Λ_ : {V : Term} → Value V → Value (Λ V)
  $ : (k : Const) → Value ($ k)
  _⟨_⟩ : {V : Term}{c : Coercion} → Value V → Inert c → Value (V ⟨ c ⟩)

------------------------------------------------------------------------
-- Type-variable substitution
------------------------------------------------------------------------

renameᵗᵐ : Renameᵗ → Term → Term
renameᵗᵐ ρ (` x) = ` x
renameᵗᵐ ρ (ƛ M) = ƛ renameᵗᵐ ρ M
renameᵗᵐ ρ (L · M) = renameᵗᵐ ρ L · renameᵗᵐ ρ M
renameᵗᵐ ρ (Λ M) = Λ (renameᵗᵐ (extᵗ ρ) M)
renameᵗᵐ ρ (L • α) = renameᵗᵐ ρ L • ρ α
renameᵗᵐ ρ (ν A N) = ν (renameᵗ ρ A) (renameᵗᵐ (extᵗ ρ) N)
renameᵗᵐ ρ ($ κ) = $ κ
renameᵗᵐ ρ (L ⊕[ op ] M) = renameᵗᵐ ρ L ⊕[ op ] renameᵗᵐ ρ M
renameᵗᵐ ρ (M ⟨ c ⟩) = renameᵗᵐ ρ M ⟨ renameᶜ ρ c ⟩
renameᵗᵐ ρ (blame ℓ) = blame ℓ

⇑ᵗᵐ : Term → Term
⇑ᵗᵐ = renameᵗᵐ suc

infixl 8 _[_]ᵀ
_[_]ᵀ : Term → TyVar → Term
M [ X ]ᵀ = renameᵗᵐ (singleRenameᵗ X) M

------------------------------------------------------------------------
-- Term-variable substitution
------------------------------------------------------------------------

Renameˣ : Set
Renameˣ = Var → Var

Substˣ : Set
Substˣ = Var → Term

extʳ : Renameˣ → Renameˣ
extʳ ρ zero = zero
extʳ ρ (suc x) = suc (ρ x)

renameˣᵐ : Renameˣ → Term → Term
renameˣᵐ ρ (` x) = ` (ρ x)
renameˣᵐ ρ (ƛ M) = ƛ renameˣᵐ (extʳ ρ) M
renameˣᵐ ρ (L · M) = renameˣᵐ ρ L · renameˣᵐ ρ M
renameˣᵐ ρ (Λ M) = Λ (renameˣᵐ ρ M)
renameˣᵐ ρ (L • α) = renameˣᵐ ρ L • α
renameˣᵐ ρ (ν A N) = ν A (renameˣᵐ ρ N)
renameˣᵐ ρ ($ κ) = $ κ
renameˣᵐ ρ (L ⊕[ op ] M) = renameˣᵐ ρ L ⊕[ op ] renameˣᵐ ρ M
renameˣᵐ ρ (M ⟨ c ⟩) = renameˣᵐ ρ M ⟨ c ⟩
renameˣᵐ ρ (blame ℓ) = blame ℓ

extˢˣ : Substˣ → Substˣ
extˢˣ σ zero = ` zero
extˢˣ σ (suc x) = renameˣᵐ suc (σ x)

↑ᵗᵐ : Substˣ → Substˣ
↑ᵗᵐ σ x = renameᵗᵐ suc (σ x)

substˣᵐ : Substˣ → Term → Term
substˣᵐ σ (` x) = σ x
substˣᵐ σ (ƛ M) = ƛ substˣᵐ (extˢˣ σ) M
substˣᵐ σ (L · M) = substˣᵐ σ L · substˣᵐ σ M
substˣᵐ σ (Λ M) = Λ (substˣᵐ (↑ᵗᵐ σ) M)
substˣᵐ σ (L • α) = substˣᵐ σ L • α
substˣᵐ σ (ν A N) = ν A (substˣᵐ (↑ᵗᵐ σ) N)
substˣᵐ σ ($ κ) = $ κ
substˣᵐ σ (L ⊕[ op ] M) = substˣᵐ σ L ⊕[ op ] substˣᵐ σ M
substˣᵐ σ (M ⟨ c ⟩) = substˣᵐ σ M ⟨ c ⟩
substˣᵐ σ (blame ℓ) = blame ℓ

singleEnv : Term → Substˣ
singleEnv N zero = N
singleEnv N (suc x) = ` x

infixl 8 _[_]
_[_] : Term → Term → Term
M [ N ] = substˣᵐ (singleEnv N) M

--------------------------------------------------------------------------------
-- Typing
--------------------------------------------------------------------------------

infix  4 _∣_∣_⊢_⦂_

data _∣_∣_⊢_⦂_ (Δ : TyCtx) (Σ : Store) (Γ : Ctx) : Term → Ty → Set₁ where

  ⊢` : ∀ {x A}
     → Γ ∋ x ⦂ A
      ----------------------
     → Δ ∣ Σ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {M A B}
     → WfTy Δ A
     → Δ ∣ Σ ∣ (A ∷ Γ) ⊢ M ⦂ B
      ----------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (ƛ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {L M A B}
     → Δ ∣ Σ ∣ Γ ⊢ L ⦂ (A ⇒ B)
     → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
      -------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (L · M) ⦂ B

  ⊢Λ : ∀ {M A} {occ : occurs zero A ≡ true}
     → Value M
     → suc Δ ∣ ⟰ᵗ Σ ∣ ⤊ᵗ Γ ⊢ M ⦂ A
      ----------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢• : ∀ {L B α}
     → Δ ∣ Σ ∣ Γ ⊢ L ⦂ (`∀ B)
     → α < Δ
      ----------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (L • α) ⦂ B [ α ]ᴿ

  ⊢ν : ∀ {N A B}
     → WfTy Δ A
     → suc Δ ∣ (0 , A) ∷ ⟰ᵗ Σ ∣ ⤊ᵗ Γ ⊢ N ⦂ ⇑ᵗ B
      -----------------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (ν A N) ⦂ B

  ⊢$ : ∀ (κ : Const)
      -------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M}
     → Δ ∣ Σ ∣ Γ ⊢ L ⦂ (‵ `ℕ)
     → (op : Prim)
     → Δ ∣ Σ ∣ Γ ⊢ M ⦂ (‵ `ℕ)
      -----------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

  ⊢⟨⟩ : ∀ {M A B c}
      → Δ ∣ Σ ⊢ c ∶ A =⇒ B
      → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
      -------------------------
      → Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢blame : ∀ {A}
      → WfTy Δ A
      → (ℓ : Label)
      ----------------------------
      → Δ ∣ Σ ∣ Γ ⊢ (blame ℓ) ⦂ A
