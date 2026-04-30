{-# OPTIONS --cumulativity --omega-in-omega #-}
module extrinsic.LogicalRelation where

-- File Charter:
--   * Defines the logical relation for extrinsic System F.
--   * Includes relation environments and logical-relatedness judgments.
--   * Exposes the core API used by parametricity and free-theorem clients.

open import Data.List using (_∷_; [])
open import Data.Nat using (zero; suc; z<s; s<s)
open import extrinsic.ProductOmega using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Level using (Setω)

open import extrinsic.Types
open import extrinsic.Terms
open import extrinsic.Reduction
open import extrinsic.Preservation using (renameᵗ-preserves-WfTy)

-- The type of relations on values of type A and B.
Rel : Ty → Ty → Setω
Rel A B =
  (V : Term) → (W : Term) →
  Value V → Value W →
  (⊢V : 0 ∣ [] ⊢ V ⦂ A) →
  (⊢W : 0 ∣ [] ⊢ W ⦂ B) →
  Setω

record RelSub : Setω where
  field
    left : Substᵗ
    right : Substᵗ
    left-closed : ∀ α → WfTy 0 (left α)
    right-closed : ∀ α → WfTy 0 (right α)
    ρR : ∀ α → Rel (left α) (right α)
open RelSub public

∅ρ : RelSub
(∅ρ .left) = λ _ → `ℕ
(∅ρ .right) = λ _ → `ℕ
(∅ρ .left-closed) = λ _ → wf`ℕ
(∅ρ .right-closed) = λ _ → wf`ℕ
(∅ρ .ρR) = λ α V W x x₁ ⊢V ⊢W → ⊥

_,⟨_,_,_,_,_⟩ : (ρ : RelSub) → (A₁ A₂ : Ty)
  → WfTy 0 A₁ → WfTy 0 A₂
  → Rel A₁ A₂ → RelSub
(ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩) .left = A₁ •ᵗ left ρ
(ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩) .right = A₂ •ᵗ right ρ
(ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩) .left-closed 0 = wfA₁
(ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩) .left-closed (suc α) = left-closed ρ α
(ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩) .right-closed 0 = wfA₂
(ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩) .right-closed (suc α) = right-closed ρ α
(ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩) .ρR 0 = R
(ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩) .ρR (suc α) = ρR ρ α

substᵗ-codom-closed :
  ∀ {Δ : TyCtx} (σ : Substᵗ)
  → (∀ α → WfTy Δ (σ α))
  → (A : Ty)
  → WfTy Δ (substᵗ σ A)
substᵗ-codom-closed {Δ = Δ} σ hσ (` α) = hσ α
substᵗ-codom-closed {Δ = Δ} σ hσ `ℕ = wf`ℕ
substᵗ-codom-closed {Δ = Δ} σ hσ `Bool = wf`Bool
substᵗ-codom-closed {Δ = Δ} σ hσ (A ⇒ B) =
  wfFn (substᵗ-codom-closed {Δ = Δ} σ hσ A)
       (substᵗ-codom-closed {Δ = Δ} σ hσ B)
substᵗ-codom-closed {Δ = Δ} σ hσ (`∀ A) =
  wf`∀
    (substᵗ-codom-closed {Δ = suc Δ} (extsᵗ σ) (exts-closed hσ) A)
  where
  exts-closed : (∀ α → WfTy Δ (σ α)) → ∀ α → WfTy (suc Δ) (extsᵗ σ α)
  exts-closed hσ 0 = wfVar z<s
  exts-closed hσ (suc α) =
    renameᵗ-preserves-WfTy (hσ α) (λ {i} i<Δ → s<s i<Δ)

--------------------------------------------------------------------------------
-- The Logical Relation
--------------------------------------------------------------------------------

𝒱 : (A : Ty) (ρ : RelSub) (V : Term) (W : Term) → Value V → Value W → Setω
ℰ : (A : Ty) (ρ : RelSub) → Term → Term → Setω

𝒱 (` α) ρ V W v w =
  Σ[ ⊢V ∈ 0 ∣ [] ⊢ V ⦂ left ρ α ]
  Σ[ ⊢W ∈ 0 ∣ [] ⊢ W ⦂ right ρ α ]
    (ρR ρ α V W v w ⊢V ⊢W)
𝒱 `ℕ ρ `zero `zero vZero vZero = ⊤
𝒱 `ℕ ρ `zero (`suc W) v0 (vSuc w) = ⊥
𝒱 `ℕ ρ (`suc V) `zero (vSuc v) v0 = ⊥
𝒱 `ℕ ρ (`suc V) (`suc W) (vSuc v) (vSuc w) = 𝒱 `ℕ ρ V W v w
𝒱 `Bool ρ `true `true vTrue vTrue = ⊤
𝒱 `Bool ρ `true `false vTrue vFalse = ⊥
𝒱 `Bool ρ `false `true vFalse vTrue = ⊥
𝒱 `Bool ρ `false `false vFalse vFalse = ⊤
𝒱 (A ⇒ B) ρ (ƛ[ C ] N) (ƛ[ D ] M) vLam vLam =
  Σ[ ⊢V ∈ 0 ∣ [] ⊢ (ƛ[ C ] N) ⦂ substᵗ (left ρ) (A ⇒ B) ]
  Σ[ ⊢W ∈ 0 ∣ [] ⊢ (ƛ[ D ] M) ⦂ substᵗ (right ρ) (A ⇒ B) ]
    (∀ {V W} (v : Value V) (w : Value W)
      → 𝒱 A ρ V W v w
      → ℰ B ρ (N [ V ]) (M [ W ]))
𝒱 (`∀ A) ρ (Λ N) (Λ M) vTlam vTlam =
  Σ[ ⊢V ∈ 0 ∣ [] ⊢ (Λ N) ⦂ substᵗ (left ρ) (`∀ A) ]
  Σ[ ⊢W ∈ 0 ∣ [] ⊢ (Λ M) ⦂ substᵗ (right ρ) (`∀ A) ]
    (∀ (A₁ A₂ : Ty)
      → (wfA₁ : WfTy 0 A₁)
      → (wfA₂ : WfTy 0 A₂)
      → (R : Rel A₁ A₂)
      → ℰ A (ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩) (N [ A₁ ]ᵀ) (M [ A₂ ]ᵀ))
𝒱 A ρ N M vN vM = ⊥

ℰ A ρ M N =
  Σ[ ⊢M ∈ 0 ∣ [] ⊢ M ⦂ substᵗ (left ρ) A ]
  Σ[ ⊢N ∈ 0 ∣ [] ⊢ N ⦂ substᵗ (right ρ) A ]
  ∃[ V ] ∃[ W ] ∃[ v ] ∃[ w ]
    (M —↠ V) × (N —↠ W) × 𝒱 A ρ V W v w

ℰ-typing : ∀ {A ρ M N}
  → ℰ A ρ M N
  → (0 ∣ [] ⊢ M ⦂ substᵗ (left ρ) A)
    × (0 ∣ [] ⊢ N ⦂ substᵗ (right ρ) A)
ℰ-typing ⟨ ⊢M , ⟨ ⊢N , _ ⟩ ⟩ = ⟨ ⊢M , ⊢N ⟩

𝒱-typing : ∀ {A ρ V W} {v : Value V} {w : Value W}
  → 𝒱 A ρ V W v w
  → (0 ∣ [] ⊢ V ⦂ substᵗ (left ρ) A)
    ×  (0 ∣ [] ⊢ W ⦂ substᵗ (right ρ) A)
𝒱-typing {A = ` α} {ρ = ρ} ⟨ ⊢V , ⟨ ⊢W , _ ⟩ ⟩ = ⟨ ⊢V , ⊢W ⟩
𝒱-typing {A = `ℕ} {V = `zero} {W = `zero} {v = v0} {w = vZero}
  _ = ⟨ ⊢zero , ⊢zero ⟩
𝒱-typing {A = `ℕ} {V = `zero} {W = `suc W} {v = v0} {w = vSuc w} ()
𝒱-typing {A = `ℕ} {V = `suc V} {W = `zero} {v = vSuc v} {w = v0} ()
𝒱-typing {A = `ℕ} {ρ = ρ} {V = `suc V} {W = `suc W} {v = vSuc v} {w = vSuc w}
  rel with 𝒱-typing {A = `ℕ} {ρ = ρ} {V = V} {W = W} {v = v} {w = w} rel
... | ⟨ ⊢V , ⊢W ⟩ = ⟨ ⊢suc ⊢V , ⊢suc ⊢W ⟩
𝒱-typing {A = `Bool} {V = `true} {W = `true} {v = vTrue} {w = vTrue}
  _ = ⟨ ⊢true , ⊢true ⟩
𝒱-typing {A = `Bool} {V = `true} {W = `false} {v = vTrue} {w = vFalse} ()
𝒱-typing {A = `Bool} {V = `false} {W = `true} {v = vFalse} {w = vTrue} ()
𝒱-typing {A = `Bool} {V = `false} {W = `false} {v = vFalse} {w = vFalse}
  _ = ⟨ ⊢false , ⊢false ⟩
𝒱-typing {A = A ⇒ B} {V = ƛ[ C ] N} {W = ƛ[ D ] M} {v = vLam} {w = vLam}
  ⟨ ⊢V , ⟨ ⊢W , _ ⟩ ⟩ = ⟨ ⊢V , ⊢W ⟩
𝒱-typing {A = A ⇒ B} {v = vLam} {w = vTrue} ()
𝒱-typing {A = A ⇒ B} {v = vLam} {w = vFalse} ()
𝒱-typing {A = A ⇒ B} {v = vLam} {w = vZero} ()
𝒱-typing {A = A ⇒ B} {v = vLam} {w = vSuc w} ()
𝒱-typing {A = A ⇒ B} {v = vLam} {w = vTlam} ()
𝒱-typing {A = A ⇒ B} {v = vTrue} ()
𝒱-typing {A = A ⇒ B} {v = vFalse} ()
𝒱-typing {A = A ⇒ B} {v = vZero} ()
𝒱-typing {A = A ⇒ B} {v = vSuc v} ()
𝒱-typing {A = A ⇒ B} {v = vTlam} ()
𝒱-typing {A = `∀ A} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam}
  ⟨ ⊢V , ⟨ ⊢W , _ ⟩ ⟩ = ⟨ ⊢V , ⊢W ⟩
𝒱-typing {A = `∀ A} {v = vTlam} {w = vLam} ()
𝒱-typing {A = `∀ A} {v = vTlam} {w = vTrue} ()
𝒱-typing {A = `∀ A} {v = vTlam} {w = vFalse} ()
𝒱-typing {A = `∀ A} {v = vTlam} {w = vZero} ()
𝒱-typing {A = `∀ A} {v = vTlam} {w = vSuc w} ()
𝒱-typing {A = `∀ A} {v = vTrue} ()
𝒱-typing {A = `∀ A} {v = vFalse} ()
𝒱-typing {A = `∀ A} {v = vZero} ()
𝒱-typing {A = `∀ A} {v = vSuc v} ()
𝒱-typing {A = `∀ A} {v = vLam} ()

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
  → ℰ A ρ
      (substᵀ (left ρ) (subst (γ .left) M))
      (substᵀ (right ρ) (subst (γ .right) N))

syntax LogicalRel Γ A M N = Γ ⊨ M ≈ N ⦂ A

--------------------------------------------------------------------------------
-- Logically related values are related terms
--------------------------------------------------------------------------------

𝒱⇒ℰ : ∀ {A} {ρ : RelSub} {V W : Term}
  → (v : Value V)
  → (w : Value W)
  → 𝒱 A ρ V W v w
  → ℰ A ρ V W
𝒱⇒ℰ {A = A} {ρ = ρ} {V = V} {W = W} v w VW-rel
  with 𝒱-typing {A = A} {ρ = ρ} {V = V} {W = W} {v = v} {w = w} VW-rel
... | ⟨ ⊢V , ⊢W ⟩ =
  ⟨ ⊢V
  , ⟨ ⊢W
    , ⟨ V
      , ⟨ W
        , ⟨ v
          , ⟨ w
            , ⟨ V ∎
              , ⟨ W ∎
                , VW-rel
                ⟩
              ⟩
            ⟩
          ⟩
        ⟩
      ⟩
    ⟩
  ⟩

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
