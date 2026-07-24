module NuTerms where

-- File Charter:
--   * Canonical syntax, values, runtime invariants, variable actions, and
--     typing for Nu GTSF terms.
--   * `Scopedᵐ` records the term-variable scope of raw syntax; `Closedᵐ` is
--     its closed-term specialization.
--   * Algebraic and typing properties belong in
--     `proof.Core.Properties.NuTermProperties`.

open import Agda.Builtin.Equality using (_≡_)
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
infixl 7 _•
infixl 7 _⟨_⟩
infixl 6 _⊕[_]_
infix  9 `_

data Term : Set where
  `_      : Var → Term
  ƛ_      : Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  _•      : Term → Term
  ν       : Ty → Term → Coercion → Term
  $       : Const → Term
  _⊕[_]_  : Term → Prim → Term → Term
  _⟨_⟩    : Term → Coercion → Term
  blame   : Term

------------------------------------------------------------------------
-- Term-variable scope
------------------------------------------------------------------------

data Scopedᵐ : ℕ → Term → Set where
  scoped-` : ∀ {k x} → x < k → Scopedᵐ k (` x)
  scoped-ƛ : ∀ {k M} → Scopedᵐ (suc k) M → Scopedᵐ k (ƛ M)
  scoped-· : ∀ {k L M} →
    Scopedᵐ k L → Scopedᵐ k M → Scopedᵐ k (L · M)
  scoped-Λ : ∀ {k M} → Scopedᵐ k M → Scopedᵐ k (Λ M)
  scoped-• : ∀ {k M} → Scopedᵐ k M → Scopedᵐ k (M •)
  scoped-ν : ∀ {k A L c} → Scopedᵐ k L → Scopedᵐ k (ν A L c)
  scoped-$ : ∀ {k κ} → Scopedᵐ k ($ κ)
  scoped-⊕ : ∀ {k L op M} →
    Scopedᵐ k L → Scopedᵐ k M → Scopedᵐ k (L ⊕[ op ] M)
  scoped-⟨⟩ : ∀ {k M c} → Scopedᵐ k M → Scopedᵐ k (M ⟨ c ⟩)
  scoped-blame : ∀ {k} → Scopedᵐ k blame

Closedᵐ : Term → Set
Closedᵐ = Scopedᵐ zero

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value : Term → Set where
  ƛ_ : (N : Term) → Value (ƛ N)
  Λ_ : {V : Term} → Value V → Value (Λ V)
  $ : (k : Const) → Value ($ k)
  _⟨_⟩ : {V : Term}{c : Coercion} → Value V → Inert c → Value (V ⟨ c ⟩)

------------------------------------------------------------------------
-- Runtime-bullet invariants
------------------------------------------------------------------------

data No• : Term → Set where
  no•-` : ∀ {x} → No• (` x)
  no•-ƛ : ∀ {M} → No• M → No• (ƛ M)
  no•-· : ∀ {L M} → No• L → No• M → No• (L · M)
  no•-Λ : ∀ {M} → No• M → No• (Λ M)
  no•-ν : ∀ {A L c} → No• L → No• (ν A L c)
  no•-$ : ∀ {κ} → No• ($ κ)
  no•-⊕ : ∀ {L op M} → No• L → No• M → No• (L ⊕[ op ] M)
  no•-⟨⟩ : ∀ {M c} → No• M → No• (M ⟨ c ⟩)
  no•-blame : No• blame

data One• : Term → Set where
  one•-here : ∀ {M} → No• M → One• (M •)
  one•-ƛ : ∀ {M} → One• M → One• (ƛ M)
  one•-·₁ : ∀ {L M} → One• L → No• M → One• (L · M)
  one•-·₂ : ∀ {L M} → No• L → One• M → One• (L · M)
  one•-Λ : ∀ {M} → One• M → One• (Λ M)
  one•-ν : ∀ {A L c} → One• L → One• (ν A L c)
  one•-⊕₁ : ∀ {L op M} → One• L → No• M → One• (L ⊕[ op ] M)
  one•-⊕₂ : ∀ {L op M} → No• L → One• M → One• (L ⊕[ op ] M)
  one•-⟨⟩ : ∀ {M c} → One• M → One• (M ⟨ c ⟩)

data AtMostOne• : Term → Set where
  zero• : ∀ {M} → No• M → AtMostOne• M
  one• : ∀ {M} → One• M → AtMostOne• M

------------------------------------------------------------------------
-- Type-variable substitution
------------------------------------------------------------------------

renameᵗᵐ : Renameᵗ → Term → Term
renameᵗᵐ ρ (` x) = ` x
renameᵗᵐ ρ (ƛ M) = ƛ renameᵗᵐ ρ M
renameᵗᵐ ρ (L · M) = renameᵗᵐ ρ L · renameᵗᵐ ρ M
renameᵗᵐ ρ (Λ M) = Λ (renameᵗᵐ (extᵗ ρ) M)
renameᵗᵐ ρ (M •) = renameᵗᵐ ρ M •
renameᵗᵐ ρ (ν A L c) =
  ν (renameᵗ ρ A) (renameᵗᵐ ρ L) (renameᶜ (extᵗ ρ) c)
renameᵗᵐ ρ ($ κ) = $ κ
renameᵗᵐ ρ (L ⊕[ op ] M) = renameᵗᵐ ρ L ⊕[ op ] renameᵗᵐ ρ M
renameᵗᵐ ρ (M ⟨ c ⟩) = renameᵗᵐ ρ M ⟨ renameᶜ ρ c ⟩
renameᵗᵐ ρ blame = blame

⇑ᵗᵐ : Term → Term
⇑ᵗᵐ = renameᵗᵐ suc

data RuntimeOK : Term → Set where
  ok-no : ∀ {M} → No• M → RuntimeOK M
  ok-• : ∀ {V} → Value V → No• V → RuntimeOK ((⇑ᵗᵐ V) •)
  ok-·₁ : ∀ {L M} → RuntimeOK L → No• M → RuntimeOK (L · M)
  ok-·₂ : ∀ {V M} → Value V → No• V → RuntimeOK M → RuntimeOK (V · M)
  ok-ν : ∀ {A L c} → RuntimeOK L → RuntimeOK (ν A L c)
  ok-⊕₁ : ∀ {L op M} → RuntimeOK L → No• M → RuntimeOK (L ⊕[ op ] M)
  ok-⊕₂ : ∀ {L op M} → Value L → No• L → RuntimeOK M
    → RuntimeOK (L ⊕[ op ] M)
  ok-⟨⟩ : ∀ {M c} → RuntimeOK M → RuntimeOK (M ⟨ c ⟩)

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
renameˣᵐ ρ (M •) = renameˣᵐ ρ M •
renameˣᵐ ρ (ν A L c) = ν A (renameˣᵐ ρ L) c
renameˣᵐ ρ ($ κ) = $ κ
renameˣᵐ ρ (L ⊕[ op ] M) = renameˣᵐ ρ L ⊕[ op ] renameˣᵐ ρ M
renameˣᵐ ρ (M ⟨ c ⟩) = renameˣᵐ ρ M ⟨ c ⟩
renameˣᵐ ρ blame = blame

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
substˣᵐ σ (M •) = substˣᵐ σ M •
substˣᵐ σ (ν A L c) = ν A (substˣᵐ σ L) c
substˣᵐ σ ($ κ) = $ κ
substˣᵐ σ (L ⊕[ op ] M) = substˣᵐ σ L ⊕[ op ] substˣᵐ σ M
substˣᵐ σ (M ⟨ c ⟩) = substˣᵐ σ M ⟨ c ⟩
substˣᵐ σ blame = blame

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

  ⊢Λ : ∀ {M A}
     → Value M
     → suc Δ ∣ ⟰ᵗ Σ ∣ ⤊ᵗ Γ ⊢ M ⦂ A
      ----------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢• : ∀ {Δ₀ Σ₀ V A C}
     → Δ ≡ suc Δ₀
     → Σ ≡ (zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ₀
     → WfTy (suc Δ₀) C
     → Value V
     → No• V
     → Δ₀ ∣ Σ₀ ∣ Γ ⊢ V ⦂ `∀ C
      ----------------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (⇑ᵗᵐ V) • ⦂ C

  ⊢ν : ∀ {L A B C c μ}
     → WfTy Δ A
     → Δ ∣ Σ ∣ Γ ⊢ L ⦂ `∀ C
     → μ ∣ suc Δ ∣ (0 , ⇑ᵗ A) ∷ ⟰ᵗ Σ ⊢ c ∶ C =⇒ ⇑ᵗ B
      --------------------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ ν A L c ⦂ B

  ⊢$ : ∀ (κ : Const)
      -------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M}
     → Δ ∣ Σ ∣ Γ ⊢ L ⦂ (‵ `ℕ)
     → (op : Prim)
     → Δ ∣ Σ ∣ Γ ⊢ M ⦂ (‵ `ℕ)
      -----------------------------------
     → Δ ∣ Σ ∣ Γ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

  ⊢⟨⟩ : ∀ {M A B c μ}
      → μ ∣ Δ ∣ Σ ⊢ c ∶ A =⇒ B
      → Δ ∣ Σ ∣ Γ ⊢ M ⦂ A
      -------------------------
      → Δ ∣ Σ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢blame : ∀ {A}
      → WfTy Δ A
      ----------------------------
      → Δ ∣ Σ ∣ Γ ⊢ blame ⦂ A
