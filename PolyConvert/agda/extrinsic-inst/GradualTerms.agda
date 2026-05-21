module GradualTerms where

-- File Charter:
--   * Term syntax and typing judgment for Gradually Typed System F (GTSF).

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import Types
open import Ctx using (⤊ᵗ)
open import Imprecision
open import Consistency
open import Primitives using (Const; Prim; constTy; κℕ)
open import proof.TypeProperties
  using (rename-raise-⇑ᵗ)

------------------------------------------------------------------------
-- Gradual precision contexts
------------------------------------------------------------------------

GPrec : VarPrecCtx → Set
GPrec Φ =
  Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    (0 ∣ Φ ⊢ p ⦂ A ⊑ B)

GPCtx : VarPrecCtx → Set
GPCtx Φ = List (GPrec Φ)

leftGTy : ∀ {Φ} → GPrec Φ → Ty
leftGTy (A , B , p , p⊢) = A

rightGTy : ∀ {Φ} → GPrec Φ → Ty
rightGTy (A , B , p , p⊢) = B

leftGCtx : ∀ {Φ} → GPCtx Φ → Ctx
leftGCtx [] = []
leftGCtx {Φ} (P ∷ Γ) = leftGTy {Φ} P ∷ leftGCtx {Φ} Γ

rightGCtx : ∀ {Φ} → GPCtx Φ → Ctx
rightGCtx [] = []
rightGCtx {Φ} (P ∷ Γ) = rightGTy {Φ} P ∷ rightGCtx {Φ} Γ

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _`[_]
infixl 6 _⊕[_]_
infix  9 `_

data GTerm : Set where
  `_      : Var → GTerm
  ƛ_⇒_    : Ty → GTerm → GTerm
  _·_     : GTerm → GTerm → GTerm
  Λ_      : GTerm → GTerm
  _`[_]   : GTerm → Ty → GTerm
  $       : Const → GTerm
  _⊕[_]_  : GTerm → Prim → GTerm → GTerm


------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data Value : GTerm → Set where
  ƛ_⇒_ :
    (A : Ty) (N : GTerm) →
    Value (ƛ A ⇒ N)

  $ :
    (κ : Const) →
    Value ($ κ)

  Λ_ :
    (N : GTerm) →
    Value (Λ N)

renameᵗᴳ : Renameᵗ → GTerm → GTerm
renameᵗᴳ ρ (` x) = ` x
renameᵗᴳ ρ (ƛ A ⇒ M) = ƛ renameᵗ ρ A ⇒ renameᵗᴳ ρ M
renameᵗᴳ ρ (L · M) = renameᵗᴳ ρ L · renameᵗᴳ ρ M
renameᵗᴳ ρ (Λ M) = Λ (renameᵗᴳ (extᵗ ρ) M)
renameᵗᴳ ρ (M `[ T ]) = renameᵗᴳ ρ M `[ renameᵗ ρ T ]
renameᵗᴳ ρ ($ κ) = $ κ
renameᵗᴳ ρ (L ⊕[ op ] M) = renameᵗᴳ ρ L ⊕[ op ] renameᵗᴳ ρ M

⇑ᵗᴳ = renameᵗᴳ suc

renameCtxAt : ℕ → Ctx → Ctx
renameCtxAt k [] = []
renameCtxAt k (A ∷ Γ) =
  renameᵗ (raiseVarFrom k) A ∷ renameCtxAt k Γ

renameCtxAt-zero :
  ∀ Γ →
  renameCtxAt zero Γ ≡ ⤊ᵗ Γ
renameCtxAt-zero [] = refl
renameCtxAt-zero (A ∷ Γ) = cong (⇑ᵗ A ∷_) (renameCtxAt-zero Γ)

renameCtxAt-⤊ᵗ :
  ∀ k Γ →
  renameCtxAt (suc k) (⤊ᵗ Γ) ≡ ⤊ᵗ (renameCtxAt k Γ)
renameCtxAt-⤊ᵗ k [] = refl
renameCtxAt-⤊ᵗ k (A ∷ Γ) =
  cong₂ _∷_ (rename-raise-⇑ᵗ k A) (renameCtxAt-⤊ᵗ k Γ)

renameᵗᴳ-cong :
  ∀ {ρ ρ′} →
  (∀ X → ρ X ≡ ρ′ X) →
  (M : GTerm) →
  renameᵗᴳ ρ M ≡ renameᵗᴳ ρ′ M
renameᵗᴳ-cong h (` x) = refl
renameᵗᴳ-cong h (ƛ A ⇒ M) =
  cong₂ ƛ_⇒_ (rename-cong h A) (renameᵗᴳ-cong h M)
renameᵗᴳ-cong h (L · M) =
  cong₂ _·_ (renameᵗᴳ-cong h L) (renameᵗᴳ-cong h M)
renameᵗᴳ-cong {ρ = ρ} {ρ′ = ρ′} h (Λ M) =
  cong Λ_ (renameᵗᴳ-cong h′ M)
  where
    h′ : ∀ X → extᵗ ρ X ≡ extᵗ ρ′ X
    h′ zero = refl
    h′ (suc X) = cong suc (h X)
renameᵗᴳ-cong h (M `[ T ]) =
  cong₂ _`[_] (renameᵗᴳ-cong h M) (rename-cong h T)
renameᵗᴳ-cong h ($ κ) = refl
renameᵗᴳ-cong h (L ⊕[ op ] M) =
  cong₂ (λ L M → L ⊕[ op ] M)
    (renameᵗᴳ-cong h L) (renameᵗᴳ-cong h M)

renameᵗᴳ-value-inv :
  ∀ {ρ M} →
  Value (renameᵗᴳ ρ M) →
  Value M
renameᵗᴳ-value-inv {M = ƛ A ⇒ M} (ƛ ._ ⇒ ._) = ƛ A ⇒ M
renameᵗᴳ-value-inv {M = Λ M} (Λ ._) = Λ M
renameᵗᴳ-value-inv {M = $ κ} ($ .κ) = $ κ

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix  4 _∣_⊢_⦂_

data _∣_⊢_⦂_ (Δ : TyCtx) (Γ : Ctx) : GTerm → Ty → Set₁ where

  ⊢` : ∀ {x A}
     → Γ ∋ x ⦂ A
     → Δ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {M A B}
     → WfTy Δ 0 A
     → Δ ∣ (A ∷ Γ) ⊢ M ⦂ B
     → Δ ∣ Γ ⊢ (ƛ A ⇒ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {L M A A′ B}
     → Δ ∣ Γ ⊢ L ⦂ (A ⇒ B)
     → Δ ∣ Γ ⊢ M ⦂ A′
     → extend-X~X Δ [] ⊢ A ~ A′
     → Δ ∣ Γ ⊢ (L · M) ⦂ B

  ⊢·★ : ∀ {L M A′}
     → Δ ∣ Γ ⊢ L ⦂ ★
     → Δ ∣ Γ ⊢ M ⦂ A′
     → extend-X~X Δ [] ⊢ A′ ~ ★
     → Δ ∣ Γ ⊢ (L · M) ⦂ ★

  ⊢Λ : ∀ {M A}
     → Value M
     → (suc Δ) ∣ (⤊ᵗ Γ) ⊢ M ⦂ A
     → Δ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢• : ∀ {M B T}
     → Δ ∣ Γ ⊢ M ⦂ (`∀ B)
     → WfTy (suc Δ) 0 B
     → WfTy Δ 0 T
     → Δ ∣ Γ ⊢ (M `[ T ]) ⦂ B [ T ]ᵗ

  ⊢$ : ∀ (κ : Const)
     → Δ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M A B}
     → Δ ∣ Γ ⊢ L ⦂ A → extend-X~X Δ [] ⊢ A ~ (‵ `ℕ)
     → (op : Prim)
     → Δ ∣ Γ ⊢ M ⦂ B → extend-X~X Δ [] ⊢ B ~ (‵ `ℕ)
     → Δ ∣ Γ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

cong-⊢ᴳ⦂ :
  ∀ {Δ Δ′ Γ Γ′ M M′ A A′} →
  Δ ≡ Δ′ →
  Γ ≡ Γ′ →
  M ≡ M′ →
  A ≡ A′ →
  Δ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ Γ′ ⊢ M′ ⦂ A′
cong-⊢ᴳ⦂ refl refl refl refl M⊢ = M⊢

