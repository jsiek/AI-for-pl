module extrinsic.Parametricity where

open import Relation.Binary.PropositionalEquality
            using    (_≡_; refl; cong; cong₂; sym; trans)
            renaming (subst to substEq)
open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (Level; Lift; lift; suc; zero)
open import Function using (case_of_)

open import extrinsic.Types
open import extrinsic.Terms
open import extrinsic.Reduction

-- The type of relations on values of type A and B
Rel : Ty → Ty → Set₁
Rel A B = (V : Term) → (W : Term) → Value V → Value W → Set

record RelSub : Set₁ where
  field
    ρ₁ : Substᵗ
    ρ₂ : Substᵗ
    ρR : ∀ α → Rel (ρ₁ α) (ρ₂ α)
open RelSub public

∅ρ : RelSub
(∅ρ .ρ₁) = idᵗ
(∅ρ .ρ₂) = idᵗ
(∅ρ .ρR) = λ α V W x x₁ → ⊥ -- wild guess! -Jeremy

_,⟨_,_,_⟩ : (ρ : RelSub) → (A₁ A₂ : Ty) → Rel A₁ A₂ → RelSub
(ρ ,⟨ A₁ , A₂ , R ⟩) .ρ₁        = A₁ •ᵗ ρ₁ ρ
(ρ ,⟨ A₁ , A₂ , R ⟩) .ρ₂        = A₂ •ᵗ ρ₂ ρ
(ρ ,⟨ A₁ , A₂ , R ⟩) .ρR 0      = R
(ρ ,⟨ A₁ , A₂ , R ⟩) .ρR (suc α)  = ρR ρ α

--------------------------------------------------------------------------------
-- The Logical Relation
--------------------------------------------------------------------------------

𝒱 : (A : Ty) (ρ : RelSub) (V : Term) (W : Term) → Value V → Value W → Set₁
ℰ : (A : Ty) (ρ : RelSub) → Term → Term → Set₁

𝒱 (` α) ρ V W v w = Lift _ (ρR ρ α V W v w)
𝒱 `ℕ ρ `zero `zero vZero vZero = ⊤
𝒱 `ℕ ρ `zero (`suc W) vZero (vSuc w) = ⊥
𝒱 `ℕ ρ (`suc V) `zero (vSuc v) vZero = ⊥
𝒱 `ℕ ρ (`suc V) (`suc W) (vSuc v) (vSuc w) = 𝒱 `ℕ ρ V W v w
𝒱 `Bool ρ `true `true vTrue vTrue = ⊤
𝒱 `Bool ρ `true `false vTrue vFalse = ⊥
𝒱 `Bool ρ `false `true vFalse vTrue = ⊥
𝒱 `Bool ρ `false `false vFalse vFalse = ⊤
𝒱 (A ⇒ B) ρ (ƛ N) (ƛ M) vLam vLam =
  ∀ {V W} (v : Value V) (w : Value W)
   → 𝒱 A ρ V W v w
   → ℰ B ρ (N [ V ]) (M [ W ])
𝒱 (`∀ A) ρ (Λ N) (Λ M) vTlam vTlam =
  ∀ (A₁ A₂ : Ty)
   → (R : Rel A₁ A₂)
   → ℰ A (ρ ,⟨ A₁ , A₂ , R ⟩) N M
𝒱 A ρ N M vN vM = ⊥

ℰ A ρ M N =
  ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
    (M —↠ V) × (N —↠ W) × 𝒱 A ρ V W v w

--------------------------------------------------------------------------------
-- Closing Substitutions
--------------------------------------------------------------------------------

record RelEnv : Set where
  field
    γ₁ : Subst
    γ₂ : Subst
open RelEnv public

∅γ : RelEnv
(∅γ .γ₁) = id
(∅γ .γ₂) = id

_,⟨_,_⟩ : (γ : RelEnv) (V : Term) (W : Term) → RelEnv
((γ ,⟨ V , W ⟩) .γ₁) = V • (γ .γ₁)
((γ ,⟨ V , W ⟩) .γ₂) = W • (γ .γ₂)


⇑γ : RelEnv → RelEnv
(⇑γ γ .γ₁) = ⇑ᵀ (γ .γ₁)
(⇑γ γ .γ₂) = ⇑ᵀ (γ .γ₂)

--------------------------------------------------------------------------------
-- Logically related contexts
--------------------------------------------------------------------------------

𝒢 : Ctx → RelSub → RelEnv → Set₁
𝒢 [] ρ γ = ⊤
𝒢 (A ∷ Γ) ρ γ = ℰ A ρ (γ .γ₁ 0) (γ .γ₂ 0) × 𝒢 Γ ρ (⇑γ γ)

𝒢-∅ : 𝒢 [] ∅ρ ∅γ
𝒢-∅ = tt

--------------------------------------------------------------------------------
-- Logically related terms
--------------------------------------------------------------------------------

LogicalRel : (Γ : Ctx) (A : Ty) (M N : Term) → Set₁
LogicalRel Γ A M N = ∀ (ρ : RelSub) (γ : RelEnv)
  → 𝒢 Γ ρ γ
  → ℰ A ρ (subst (γ .γ₁) M) (subst (γ .γ₂) N)

postulate
  fundamental : ∀ {Δ Γ A M} → Δ ⊢ Γ ⊢ M ⦂ A → LogicalRel Γ A M M

