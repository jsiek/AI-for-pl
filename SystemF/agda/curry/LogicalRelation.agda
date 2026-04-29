{-# OPTIONS --cumulativity --omega-in-omega #-}
module curry.LogicalRelation where

-- File Charter:
--   * Defines the public logical relation interface for curry System F.
--   * Includes relation environments, logical-relatedness judgments, and context builders.
--   * Keeps renaming/substitution proof infrastructure in `curry.proof.LogicalRelation`.

open import Data.List using (_∷_; [])
open import Data.Nat using (zero; suc)
open import curry.ProductOmega using (Σ-syntax; ∃-syntax; _×_)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Level using (Setω)

open import curry.Types
open import curry.Terms
open import curry.Reduction

-- The type of relations on values of type A and B
Rel : Ty → Ty → Setω
Rel A B = (V : Term) → (W : Term) → Value V → Value W → Setω  -- omega-in-omega needed here

record RelSub : Setω where
  field
    left : Substᵗ
    right : Substᵗ
    ρR : ∀ α → Rel (left α) (right α)
open RelSub public

∅ρ : RelSub
(∅ρ .left) = idᵗ
(∅ρ .right) = idᵗ
(∅ρ .ρR) = λ α V W x x₁ → ⊥

_,⟨_,_,_⟩ : (ρ : RelSub) → (A₁ A₂ : Ty) → Rel A₁ A₂ → RelSub
(ρ ,⟨ A₁ , A₂ , R ⟩) .left = A₁ •ᵗ left ρ
(ρ ,⟨ A₁ , A₂ , R ⟩) .right = A₂ •ᵗ right ρ
(ρ ,⟨ A₁ , A₂ , R ⟩) .ρR 0 = R
(ρ ,⟨ A₁ , A₂ , R ⟩) .ρR (suc α) = ρR ρ α

--------------------------------------------------------------------------------
-- The Logical Relation
--------------------------------------------------------------------------------

𝒱 : (A : Ty) (ρ : RelSub) (V : Term) (W : Term) → Value V → Value W → Setω
ℰ : (A : Ty) (ρ : RelSub) → Term → Term → Setω

𝒱 (` α) ρ V W v w = ρR ρ α V W v w
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
    left : Subst
    right : Subst
open RelEnv public

∅γ : RelEnv
(∅γ .left) = id
(∅γ .right) = id

_,⟨_,_⟩ : (γ : RelEnv) (V : Term) (W : Term) → RelEnv
(γ ,⟨ V , W ⟩) .left = V • (γ .left)
(γ ,⟨ V , W ⟩) .right = W • (γ .right)

⇓γ : RelEnv → RelEnv
(⇓γ γ .left) i = left γ (suc i)
(⇓γ γ .right) i = right γ (suc i)

--------------------------------------------------------------------------------
-- Logically related contexts
--------------------------------------------------------------------------------

𝒢 : Ctx → RelSub → RelEnv → Setω
𝒢 [] ρ γ = ⊤
𝒢 (A ∷ Γ) ρ γ = ℰ A ρ (γ .left 0) (γ .right 0) × 𝒢 Γ ρ (⇓γ γ)

--------------------------------------------------------------------------------
-- Logically related terms
--------------------------------------------------------------------------------

LogicalRel : (Γ : Ctx) (A : Ty) (M N : Term) → Setω
LogicalRel Γ A M N = ∀ (ρ : RelSub) (γ : RelEnv)
  → 𝒢 Γ ρ γ
  → ℰ A ρ (subst (γ .left) M) (subst (γ .right) N)

syntax LogicalRel Γ A M N = Γ ⊨ M ≈ N ⦂ A

--------------------------------------------------------------------------------
-- Logically related values are related terms
--------------------------------------------------------------------------------

𝒱⇒ℰ : ∀ {A} {ρ : RelSub} {V W : Term}
  → (v : Value V)
  → (w : Value W)
  → 𝒱 A ρ V W v w
  → ℰ A ρ V W
𝒱⇒ℰ {V = V} {W = W} v w VW-rel =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ V ∎ , ⟨ W ∎ , VW-rel ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

--------------------------------------------------------------------------------
-- Constructing logically related contexts
--------------------------------------------------------------------------------

𝒢-∅ : 𝒢 [] ∅ρ ∅γ
𝒢-∅ = tt

𝒢-extend : ∀ {Γ A} {ρ : RelSub} {γ : RelEnv} {V W : Term}
  → (env : 𝒢 Γ ρ γ)
  → (v : Value V)
  → (w : Value W)
  → 𝒱 A ρ V W v w
  → 𝒢 (A ∷ Γ) ρ (γ ,⟨ V , W ⟩)
𝒢-extend {A = A} {ρ = ρ} {V = V} {W = W} env v w VW-rel =
  ⟨ 𝒱⇒ℰ {A = A} {ρ = ρ} {V = V} {W = W} v w VW-rel , env ⟩
