{-# OPTIONS --cumulativity --omega-in-omega #-}
module extrinsic.LogicalRelation where

-- File Charter:
--   * Defines the logical relation for extrinsic System F.
--   * Includes relation environments and logical-relatedness judgments.
--   * Proves helper lemmas for renaming/substitution and environment lifting.

open import Data.List using (_∷_; [])
open import Data.Nat using (zero; suc)
open import extrinsic.ProductOmega using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Level using (Setω)

open import extrinsic.Types
open import extrinsic.Terms
open import extrinsic.Reduction

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
(ρ ,⟨ A₁ , A₂ , R ⟩) .left      = A₁ •ᵗ left ρ
(ρ ,⟨ A₁ , A₂ , R ⟩) .right     = A₂ •ᵗ right ρ
(ρ ,⟨ A₁ , A₂ , R ⟩) .ρR 0      = R
(ρ ,⟨ A₁ , A₂ , R ⟩) .ρR (suc α)  = ρR ρ α

--------------------------------------------------------------------------------
-- The Logical Relation
--------------------------------------------------------------------------------

𝒱 : (A : Ty) (ρ : RelSub) (V : Term) (W : Term) → Value V → Value W → Setω
ℰ : (A : Ty) (ρ : RelSub) → Term → Term → Setω

𝒱 (` α) ρ V W v w = (ρR ρ α V W v w)
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
((γ ,⟨ V , W ⟩) .left) = V • (γ .left)
((γ ,⟨ V , W ⟩) .right) = W • (γ .right)


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

--------------------------------------------------------------------------------
-- Renaming type variables in the logical relation
--------------------------------------------------------------------------------

data WkRel : Renameᵗ → RelSub → RelSub → Setω where
  wk-suc :
    ∀ {ρ A₁ A₂} (R : Rel A₁ A₂) →
    WkRel suc ρ (ρ ,⟨ A₁ , A₂ , R ⟩)

  wk-ext :
    ∀ {ξ ρ ρ' B₁ B₂} (S : Rel B₁ B₂) →
    WkRel ξ ρ ρ' →
    WkRel (extᵗ ξ) (ρ ,⟨ B₁ , B₂ , S ⟩) (ρ' ,⟨ B₁ , B₂ , S ⟩)

wk-ρR-cast : ∀ {ξ ρ ρ'} → WkRel ξ ρ ρ' → (α : Var)
  → ∀ {V W} {v : Value V} {w : Value W}
  → ρR ρ α V W v w
  → ρR ρ' (ξ α) V W v w
wk-ρR-cast (wk-suc R) α rel = rel
wk-ρR-cast (wk-ext _ wk-r) zero rel = rel
wk-ρR-cast (wk-ext _ wk-r) (suc α) rel = wk-ρR-cast wk-r α rel

wk-ρR-uncast : ∀ {ξ ρ ρ'} → WkRel ξ ρ ρ' → (α : Var)
  → ∀ {V W} {v : Value V} {w : Value W}
  → ρR ρ' (ξ α) V W v w
  → ρR ρ α V W v w
wk-ρR-uncast (wk-suc R) α rel = rel
wk-ρR-uncast (wk-ext _ wk-r) zero rel = rel
wk-ρR-uncast (wk-ext _ wk-r) (suc α) rel = wk-ρR-uncast wk-r α rel

𝒱-Nat-irrel : ∀ {ρ σ V W} {v : Value V} {w : Value W}
  → 𝒱 `ℕ ρ V W v w
  → 𝒱 `ℕ σ V W v w
𝒱-Nat-irrel {V = `zero} {W = `zero} {v = vZero} {w = vZero} VW-rel = VW-rel
𝒱-Nat-irrel {V = `suc V} {W = `suc W} {v = vSuc v} {w = vSuc w} VW-rel =
  𝒱-Nat-irrel {V = V} {W = W} {v = v} {w = w} VW-rel

𝒱-Bool-irrel : ∀ {ρ σ V W} {v : Value V} {w : Value W}
  → 𝒱 `Bool ρ V W v w
  → 𝒱 `Bool σ V W v w
𝒱-Bool-irrel {V = `true} {W = `true} {v = vTrue} {w = vTrue} VW-rel = VW-rel
𝒱-Bool-irrel {V = `false} {W = `false} {v = vFalse} {w = vFalse} VW-rel = VW-rel

mutual
  𝒱-rename-wk :
    ∀ {A ξ ρ ρ' V W} {v : Value V} {w : Value W}
    → WkRel ξ ρ ρ'
    → 𝒱 A ρ V W v w
    → 𝒱 (renameᵗ ξ A) ρ' V W v w
  𝒱-rename-wk {A = ` α} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    wk-ρR-cast {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r α {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-rename-wk {A = `ℕ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    𝒱-Nat-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-rename-wk {A = `Bool} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    𝒱-Bool-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-rename-wk {A = A ⇒ B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = ƛ N} {W = ƛ M} {v = vLam} {w = vLam} wk-r 𝒱VW =
    λ v₁ w₁ arg-rel' →
      ℰ-rename-wk {A = B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
        (𝒱VW v₁ w₁
          (𝒱-unrename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {v = v₁} {w = w₁} wk-r arg-rel'))
  𝒱-rename-wk {A = A ⇒ B} {v = vLam} {w = vTrue} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vLam} {w = vFalse} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vLam} {w = vZero} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vLam} {w = vSuc w} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vLam} {w = vTlam} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vTrue} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vFalse} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vZero} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vSuc v} wk-r ()
  𝒱-rename-wk {A = A ⇒ B} {v = vTlam} wk-r ()
  𝒱-rename-wk {A = `∀ A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam} wk-r 𝒱VW =
    λ A₁ A₂ R →
      ℰ-rename-wk {A = A} {ξ = extᵗ ξ} {ρ = ρ ,⟨ A₁ , A₂ , R ⟩} {ρ' = ρ' ,⟨ A₁ , A₂ , R ⟩}
        (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r)
        (𝒱VW A₁ A₂ R)
  𝒱-rename-wk {A = `∀ A} {v = vTlam} {w = vLam} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vTlam} {w = vTrue} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vTlam} {w = vFalse} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vTlam} {w = vZero} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vTlam} {w = vSuc w} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vTrue} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vFalse} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vZero} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vSuc v} wk-r ()
  𝒱-rename-wk {A = `∀ A} {v = vLam} wk-r ()

  𝒱-unrename-wk :
    ∀ {A ξ ρ ρ' V W} {v : Value V} {w : Value W}
    → WkRel ξ ρ ρ'
    → 𝒱 (renameᵗ ξ A) ρ' V W v w
    → 𝒱 A ρ V W v w
  𝒱-unrename-wk {A = ` α} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    wk-ρR-uncast {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r α {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-unrename-wk {A = `ℕ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    𝒱-Nat-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-unrename-wk {A = `Bool} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    𝒱-Bool-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-unrename-wk {A = A ⇒ B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = ƛ N} {W = ƛ M} {v = vLam} {w = vLam} wk-r 𝒱VW =
    λ v₁ w₁ arg-rel →
      ℰ-unrename-wk {A = B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
        (𝒱VW v₁ w₁
          (𝒱-rename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {v = v₁} {w = w₁} wk-r arg-rel))
  𝒱-unrename-wk {A = A ⇒ B} {v = vLam} {w = vTrue} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vLam} {w = vFalse} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vLam} {w = vZero} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vLam} {w = vSuc w} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vLam} {w = vTlam} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vTrue} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vFalse} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vZero} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vSuc v} wk-r ()
  𝒱-unrename-wk {A = A ⇒ B} {v = vTlam} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam} wk-r 𝒱VW =
    λ A₁ A₂ R →
      ℰ-unrename-wk {A = A} {ξ = extᵗ ξ} {ρ = ρ ,⟨ A₁ , A₂ , R ⟩} {ρ' = ρ' ,⟨ A₁ , A₂ , R ⟩}
        (wk-ext {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂} R wk-r)
        (𝒱VW A₁ A₂ R)
  𝒱-unrename-wk {A = `∀ A} {v = vTlam} {w = vLam} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vTlam} {w = vTrue} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vTlam} {w = vFalse} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vTlam} {w = vZero} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vTlam} {w = vSuc w} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vTrue} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vFalse} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vZero} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vSuc v} wk-r ()
  𝒱-unrename-wk {A = `∀ A} {v = vLam} wk-r ()

  ℰ-rename-wk :
    ∀ {A ξ ρ ρ' M N}
    → WkRel ξ ρ ρ'
    → ℰ A ρ M N
    → ℰ (renameᵗ ξ A) ρ' M N
  ℰ-rename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W
      , 𝒱-rename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW
      ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

  ℰ-unrename-wk :
    ∀ {A ξ ρ ρ' M N}
    → WkRel ξ ρ ρ'
    → ℰ (renameᵗ ξ A) ρ' M N
    → ℰ A ρ M N
  ℰ-unrename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W
      , 𝒱-unrename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW
      ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

⇑-ℰ : ∀{A A₁ A₂}{ρ : RelSub}{γ : RelEnv}{R : Rel A₁ A₂}
  → ℰ A ρ (γ .left 0) (γ .right 0)
  → ℰ (renameᵗ suc A) (ρ ,⟨ A₁ , A₂ , R ⟩) (γ .left 0) (γ .right 0)
⇑-ℰ {A}{A₁}{A₂}{ρ}{γ}{R} ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ →V , ⟨ →W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ →V , ⟨ →W , 𝒱-rename-wk{A} (wk-suc R) 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

liftRelEnv-related : ∀ {Γ A₁ A₂} {ρ : RelSub} {γ : RelEnv}
    (R : Rel A₁ A₂)
  → 𝒢 Γ ρ γ
  → 𝒢 (⤊ Γ) (ρ ,⟨ A₁ , A₂ , R ⟩) γ
liftRelEnv-related {[]} R G = tt
liftRelEnv-related {A ∷ Γ} {A₁ = A₁} {A₂ = A₂} {ρ} {γ} R G =
  ⟨ ⇑-ℰ {A = A} {A₁ = A₁} {A₂ = A₂} {ρ = ρ} {γ = γ} {R = R} (G .proj₁)
  , liftRelEnv-related {Γ} {A₁ = A₁} {A₂ = A₂} {ρ = ρ} {γ = ⇓γ γ} R (G .proj₂)
  ⟩

--------------------------------------------------------------------------------
-- Substituting type variables in the logical relation
--------------------------------------------------------------------------------

record SubstRel (σ : Substᵗ) (ρ : RelSub) (ρ' : RelSub) : Setω where
  field
    var⇒ : ∀ α {V W} {v : Value V} {w : Value W}
      → 𝒱 (` α) ρ' V W v w
      → 𝒱 (σ α) ρ V W v w

    var⇐ : ∀ α {V W} {v : Value V} {w : Value W}
      → 𝒱 (σ α) ρ V W v w
      → 𝒱 (` α) ρ' V W v w

exts-SubstRel : ∀ {σ ρ ρ' A₁ A₂}
  → (R : Rel A₁ A₂)
  → SubstRel σ ρ ρ'
  → SubstRel (extsᵗ σ) (ρ ,⟨ A₁ , A₂ , R ⟩) (ρ' ,⟨ A₁ , A₂ , R ⟩)
SubstRel.var⇒ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) zero rel = rel
SubstRel.var⇒ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) (suc α) rel =
  𝒱-rename-wk {A = σ α} {ξ = suc} {ρ = ρ} {ρ' = ρ ,⟨ A₁ , A₂ , R ⟩}
    (wk-suc {ρ = ρ} {A₁ = A₁} {A₂ = A₂} R)
    (SubstRel.var⇒ sr α rel)

SubstRel.var⇐ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) zero rel = rel
SubstRel.var⇐ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} R sr) (suc α) rel =
  SubstRel.var⇐ sr α
    (𝒱-unrename-wk {A = σ α} {ξ = suc} {ρ = ρ} {ρ' = ρ ,⟨ A₁ , A₂ , R ⟩}
      (wk-suc {ρ = ρ} {A₁ = A₁} {A₂ = A₂} R)
      rel)

mutual
  𝒱-subst :
    ∀ {A σ ρ ρ' V W} {v : Value V} {w : Value W}
    → SubstRel σ ρ ρ'
    → 𝒱 A ρ' V W v w
    → 𝒱 (substᵗ σ A) ρ V W v w
  𝒱-subst {A = ` α} sr 𝒱VW = SubstRel.var⇒ sr α 𝒱VW
  𝒱-subst {A = `ℕ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW =
    𝒱-Nat-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-subst {A = `Bool} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW =
    𝒱-Bool-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-subst {A = A ⇒ B} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = ƛ N} {W = ƛ M} {v = vLam} {w = vLam} sr 𝒱VW =
    λ v₁ w₁ arg-rel →
      ℰ-subst {A = B} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
        (𝒱VW v₁ w₁ (𝒱-unsubst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {v = v₁} {w = w₁} sr arg-rel))
  𝒱-subst {A = A ⇒ B} {v = vLam} {w = vTrue} sr ()
  𝒱-subst {A = A ⇒ B} {v = vLam} {w = vFalse} sr ()
  𝒱-subst {A = A ⇒ B} {v = vLam} {w = vZero} sr ()
  𝒱-subst {A = A ⇒ B} {v = vLam} {w = vSuc w} sr ()
  𝒱-subst {A = A ⇒ B} {v = vLam} {w = vTlam} sr ()
  𝒱-subst {A = A ⇒ B} {v = vTrue} sr ()
  𝒱-subst {A = A ⇒ B} {v = vFalse} sr ()
  𝒱-subst {A = A ⇒ B} {v = vZero} sr ()
  𝒱-subst {A = A ⇒ B} {v = vSuc v} sr ()
  𝒱-subst {A = A ⇒ B} {v = vTlam} sr ()
  𝒱-subst {A = `∀ A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam} sr 𝒱VW =
    λ A₁ A₂ R →
      ℰ-subst {A = A} {σ = extsᵗ σ}
        {ρ = ρ ,⟨ A₁ , A₂ , R ⟩}
        {ρ' = ρ' ,⟨ A₁ , A₂ , R ⟩}
        (exts-SubstRel R sr)
        (𝒱VW A₁ A₂ R)
  𝒱-subst {A = `∀ A} {v = vTlam} {w = vLam} sr ()
  𝒱-subst {A = `∀ A} {v = vTlam} {w = vTrue} sr ()
  𝒱-subst {A = `∀ A} {v = vTlam} {w = vFalse} sr ()
  𝒱-subst {A = `∀ A} {v = vTlam} {w = vZero} sr ()
  𝒱-subst {A = `∀ A} {v = vTlam} {w = vSuc w} sr ()
  𝒱-subst {A = `∀ A} {v = vTrue} sr ()
  𝒱-subst {A = `∀ A} {v = vFalse} sr ()
  𝒱-subst {A = `∀ A} {v = vZero} sr ()
  𝒱-subst {A = `∀ A} {v = vSuc v} sr ()
  𝒱-subst {A = `∀ A} {v = vLam} sr ()

  𝒱-unsubst :
    ∀ {A σ ρ ρ' V W} {v : Value V} {w : Value W}
    → SubstRel σ ρ ρ'
    → 𝒱 (substᵗ σ A) ρ V W v w
    → 𝒱 A ρ' V W v w
  𝒱-unsubst {A = ` α} sr 𝒱VW = SubstRel.var⇐ sr α 𝒱VW
  𝒱-unsubst {A = `ℕ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW =
    𝒱-Nat-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-unsubst {A = `Bool} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW =
    𝒱-Bool-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-unsubst {A = A ⇒ B} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = ƛ N} {W = ƛ M} {v = vLam} {w = vLam} sr 𝒱VW =
    λ v₁ w₁ arg-rel →
      ℰ-unsubst {A = B} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
        (𝒱VW v₁ w₁ (𝒱-subst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {v = v₁} {w = w₁} sr arg-rel))
  𝒱-unsubst {A = A ⇒ B} {v = vLam} {w = vTrue} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vLam} {w = vFalse} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vLam} {w = vZero} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vLam} {w = vSuc w} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vLam} {w = vTlam} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vTrue} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vFalse} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vZero} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vSuc v} sr ()
  𝒱-unsubst {A = A ⇒ B} {v = vTlam} sr ()
  𝒱-unsubst {A = `∀ A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam} sr 𝒱VW =
    λ A₁ A₂ R →
      ℰ-unsubst {A = A} {σ = extsᵗ σ}
        {ρ = ρ ,⟨ A₁ , A₂ , R ⟩}
        {ρ' = ρ' ,⟨ A₁ , A₂ , R ⟩}
        (exts-SubstRel R sr)
        (𝒱VW A₁ A₂ R)
  𝒱-unsubst {A = `∀ A} {v = vTlam} {w = vLam} sr ()
  𝒱-unsubst {A = `∀ A} {v = vTlam} {w = vTrue} sr ()
  𝒱-unsubst {A = `∀ A} {v = vTlam} {w = vFalse} sr ()
  𝒱-unsubst {A = `∀ A} {v = vTlam} {w = vZero} sr ()
  𝒱-unsubst {A = `∀ A} {v = vTlam} {w = vSuc w} sr ()
  𝒱-unsubst {A = `∀ A} {v = vTrue} sr ()
  𝒱-unsubst {A = `∀ A} {v = vFalse} sr ()
  𝒱-unsubst {A = `∀ A} {v = vZero} sr ()
  𝒱-unsubst {A = `∀ A} {v = vSuc v} sr ()
  𝒱-unsubst {A = `∀ A} {v = vLam} sr ()

  ℰ-subst :
    ∀ {A σ ρ ρ' M N}
    → SubstRel σ ρ ρ'
    → ℰ A ρ' M N
    → ℰ (substᵗ σ A) ρ M N
  ℰ-subst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W
      , 𝒱-subst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW
      ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

  ℰ-unsubst :
    ∀ {A σ ρ ρ' M N}
    → SubstRel σ ρ ρ'
    → ℰ (substᵗ σ A) ρ M N
    → ℰ A ρ' M N
  ℰ-unsubst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W
      , 𝒱-unsubst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW
      ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
