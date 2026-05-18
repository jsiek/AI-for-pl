module GradualTerms where

-- File Charter:
--   * Extrinsic term syntax and typing judgment for Gradually Typed System F (GTSF).

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import Types
open import Ctx using (⤊ᵗ)
open import Imprecision
  using
    ( Imp
    ; plains
    ; _∣_⊢_⦂_⊑_
    )
open import Consistency
open import Primitives using (Const; Prim; constTy; κℕ)
open import proof.TypeProperties
  using (rename-raise-⇑ᵗ)

------------------------------------------------------------------------
-- Gradual precision contexts
------------------------------------------------------------------------

GPrec : TyCtx → Set
GPrec Δ =
  Σ[ A ∈ Ty ] Σ[ B ∈ Ty ] Σ[ p ∈ Imp ]
    (0 ∣ plains Δ [] ⊢ p ⦂ A ⊑ B)

GPCtx : TyCtx → Set
GPCtx Δ = List (GPrec Δ)

leftGTy : ∀ {Δ} → GPrec Δ → Ty
leftGTy (A , B , p , p⊢) = A

rightGTy : ∀ {Δ} → GPrec Δ → Ty
rightGTy (A , B , p , p⊢) = B

leftGCtx : ∀ {Δ} → GPCtx Δ → Ctx
leftGCtx [] = []
leftGCtx (P ∷ Γ) = leftGTy P ∷ leftGCtx Γ

rightGCtx : ∀ {Δ} → GPCtx Δ → Ctx
rightGCtx [] = []
rightGCtx (P ∷ Γ) = rightGTy P ∷ rightGCtx Γ

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

data _∣_⊢_⦂_ (Δ : TyCtx) (Γ : Ctx) : GTerm → Ty → Set where

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
     → boths Δ [] ⊢ A ~ A′
     → Δ ∣ Γ ⊢ (L · M) ⦂ B

  ⊢·★ : ∀ {L M A′}
     → Δ ∣ Γ ⊢ L ⦂ ★
     → Δ ∣ Γ ⊢ M ⦂ A′
     → boths Δ [] ⊢ A′ ~ ★
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
     
  ⊢•★ : ∀ {M T}
     → Δ ∣ Γ ⊢ M ⦂ ★
     → WfTy 0 0 T
     → Δ ∣ Γ ⊢ (M `[ T ]) ⦂ ★

  ⊢$ : ∀ (κ : Const)
     → Δ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M A B}
     → Δ ∣ Γ ⊢ L ⦂ A → boths Δ [] ⊢ A ~ (‵ `ℕ)
     → (op : Prim)
     → Δ ∣ Γ ⊢ M ⦂ B → boths Δ [] ⊢ B ~ (‵ `ℕ)
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

------------------------------------------------------------------------
-- Gradual-term imprecision
------------------------------------------------------------------------

infix 4 _⊢ᴳ_⊑_
data _⊢ᴳ_⊑_ (Δ : TyCtx) : GTerm → GTerm → Set where

  ⊑` : ∀ {x} →
    Δ ⊢ᴳ (` x) ⊑ (` x)

  ⊑ƛ : ∀ {A A′ M M′ pA} →
    0 ∣ plains Δ [] ⊢ pA ⦂ A ⊑ A′ →
    Δ ⊢ᴳ M ⊑ M′ →
    Δ ⊢ᴳ (ƛ A ⇒ M) ⊑ (ƛ A′ ⇒ M′)

  ⊑· : ∀ {L L′ M M′} →
    Δ ⊢ᴳ L ⊑ L′ →
    Δ ⊢ᴳ M ⊑ M′ →
    Δ ⊢ᴳ (L · M) ⊑ (L′ · M′)

  ⊑Λ : ∀ {M M′} →
    Value M →
    Value M′ →
    suc Δ ⊢ᴳ M ⊑ M′ →
    Δ ⊢ᴳ (Λ M) ⊑ (Λ M′)

  ⊑ΛL : ∀ {M M′} →
    Value M →
    suc Δ ⊢ᴳ M ⊑ renameᵗᴳ suc M′ →
    Δ ⊢ᴳ (Λ M) ⊑ M′

  ⊑`[] : ∀ {M M′ T T′ pT} →
    Δ ⊢ᴳ M ⊑ M′ →
    0 ∣ plains Δ [] ⊢ pT ⦂ T ⊑ T′ →
    Δ ⊢ᴳ (M `[ T ]) ⊑ (M′ `[ T′ ])

  ⊑`[]L : ∀ {M M′ T} →
    Δ ⊢ᴳ M ⊑ M′ →
    WfTy 0 0 T →
    Δ ⊢ᴳ (M `[ T ]) ⊑ M′

  ⊑$ : ∀ {n} →
    Δ ⊢ᴳ ($ (κℕ n)) ⊑ ($ (κℕ n))

  ⊑⊕ : ∀ {L L′ M M′ op} →
    Δ ⊢ᴳ L ⊑ L′ →
    Δ ⊢ᴳ M ⊑ M′ →
    Δ ⊢ᴳ (L ⊕[ op ] M) ⊑ (L′ ⊕[ op ] M′)
