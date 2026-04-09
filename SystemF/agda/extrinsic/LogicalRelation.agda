{-# OPTIONS --cumulativity --omega-in-omega #-}
module extrinsic.LogicalRelation where

-- File Charter:
--   * Defines the logical relation for extrinsic System F.
--   * Includes relation environments and logical-relatedness judgments.
--   * Proves helper lemmas for renaming/substitution and environment lifting.

open import Data.List using (_∷_; [])
open import Data.Nat using (zero; suc; z<s; s<s)
open import extrinsic.ProductOmega using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Level using (Setω)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
  renaming (subst to substEq)

open import extrinsic.Types
open import extrinsic.TypeSubst as TS
open import extrinsic.TypeTermSubst using (substᵀ-id-typed)
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

--------------------------------------------------------------------------------
-- Renaming type variables in the logical relation
--------------------------------------------------------------------------------

ℰ-close-ρ :
  ∀ {A : Ty} {ρ : RelSub} {M N : Term}
  → ℰ A ρ M N
  → ℰ A ρ (substᵀ (left ρ) M) (substᵀ (right ρ) N)
ℰ-close-ρ {A = A} {ρ = ρ} {M = M} {N = N}
  ⟨ ⊢M , ⟨ ⊢N , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ substEq (λ Tm → 0 ∣ [] ⊢ Tm ⦂ substᵗ (left ρ) A)
      (sym (substᵀ-id-typed (λ ()) ⊢M)) ⊢M
  , ⟨ substEq (λ Tm → 0 ∣ [] ⊢ Tm ⦂ substᵗ (right ρ) A)
        (sym (substᵀ-id-typed (λ ()) ⊢N)) ⊢N
    , ⟨ V , ⟨ W , ⟨ v , ⟨ w
      , ⟨ substEq (λ Tm → Tm —↠ V) (sym (substᵀ-id-typed (λ ()) ⊢M)) M—↠V
        , ⟨ substEq (λ Tm → Tm —↠ W) (sym (substᵀ-id-typed (λ ()) ⊢N)) N—↠W
          , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

data WkRel : Renameᵗ → RelSub → RelSub → Setω where
  wk-suc :
    ∀ {ρ A₁ A₂} (wfA₁ : WfTy 0 A₁) (wfA₂ : WfTy 0 A₂) (R : Rel A₁ A₂) →
    WkRel suc ρ (ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩)

  wk-ext :
    ∀ {ξ ρ ρ' B₁ B₂}
      (hB₁ : WfTy 0 B₁) (hB₂ : WfTy 0 B₂)
      (S : Rel B₁ B₂) →
    WkRel ξ ρ ρ' →
    WkRel (extᵗ ξ)
      (ρ ,⟨ B₁ , B₂ , hB₁ , hB₂ , S ⟩)
      (ρ' ,⟨ B₁ , B₂ , hB₁ , hB₂ , S ⟩)

wk-left-var :
  ∀ {ξ : Renameᵗ} {ρ ρ' : RelSub}
  → WkRel ξ ρ ρ'
  → (α : Var)
  → RelSub.left ρ α ≡ᵗ RelSub.left ρ' (ξ α)
wk-left-var (wk-suc _ _ R) α = refl
wk-left-var (wk-ext _ _ _ wk-r) 0 = refl
wk-left-var (wk-ext _ _ _ wk-r) (suc α) = wk-left-var wk-r α

wk-right-var :
  ∀ {ξ : Renameᵗ} {ρ ρ' : RelSub}
  → WkRel ξ ρ ρ'
  → (α : Var)
  → RelSub.right ρ α ≡ᵗ RelSub.right ρ' (ξ α)
wk-right-var (wk-suc _ _ R) α = refl
wk-right-var (wk-ext _ _ _ wk-r) 0 = refl
wk-right-var (wk-ext _ _ _ wk-r) (suc α) = wk-right-var wk-r α

wk-left-subst : ∀ {ξ ρ ρ'} → WkRel ξ ρ ρ' → (A : Ty)
  → substᵗ (RelSub.left ρ') (renameᵗ ξ A) ≡ substᵗ (RelSub.left ρ) A
wk-left-subst {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r A =
  trans
    (TS.rename-subst-commute ξ (RelSub.left ρ') A)
    (TS.subst-cong (λ α → sym (wk-left-var wk-r α)) A)

wk-right-subst : ∀ {ξ ρ ρ'} → WkRel ξ ρ ρ' → (A : Ty)
  → substᵗ (RelSub.right ρ') (renameᵗ ξ A) ≡ substᵗ (RelSub.right ρ) A
wk-right-subst {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r A =
  trans
    (TS.rename-subst-commute ξ (RelSub.right ρ') A)
    (TS.subst-cong (λ α → sym (wk-right-var wk-r α)) A)

wk-ρR-cast : ∀ {ξ ρ ρ'} → (wk-r : WkRel ξ ρ ρ') → (α : Var)
  → ∀ {V W} {v : Value V} {w : Value W} {⊢V : 0 ∣ [] ⊢ V ⦂ RelSub.left ρ α} {⊢W : 0 ∣ [] ⊢ W ⦂ RelSub.right ρ α}
  → ρR ρ α V W v w ⊢V ⊢W
  → ρR ρ' (ξ α) V W v w
      (substEq (λ T → 0 ∣ [] ⊢ V ⦂ T) (wk-left-var wk-r α) ⊢V)
      (substEq (λ T → 0 ∣ [] ⊢ W ⦂ T) (wk-right-var wk-r α) ⊢W)
wk-ρR-cast (wk-suc _ _ R) α rel = rel
wk-ρR-cast (wk-ext _ _ _ wk-r) 0 rel = rel
wk-ρR-cast (wk-ext _ _ _ wk-r) (suc α) rel = wk-ρR-cast wk-r α rel

wk-ρR-uncast : ∀ {ξ ρ ρ'} → (wk-r : WkRel ξ ρ ρ') → (α : Var)
  → ∀ {V W} {v : Value V} {w : Value W} {⊢V : 0 ∣ [] ⊢ V ⦂ RelSub.left ρ' (ξ α)} {⊢W : 0 ∣ [] ⊢ W ⦂ RelSub.right ρ' (ξ α)}
  → ρR ρ' (ξ α) V W v w ⊢V ⊢W
  → ρR ρ α V W v w
      (substEq (λ T → 0 ∣ [] ⊢ V ⦂ T) (sym (wk-left-var wk-r α)) ⊢V)
      (substEq (λ T → 0 ∣ [] ⊢ W ⦂ T) (sym (wk-right-var wk-r α)) ⊢W)
wk-ρR-uncast (wk-suc _ _ R) α rel = rel
wk-ρR-uncast (wk-ext _ _ _ wk-r) 0 rel = rel
wk-ρR-uncast (wk-ext _ _ _ wk-r) (suc α) rel = wk-ρR-uncast wk-r α rel

𝒱-Nat-irrel : ∀ {ρ σ V W} {v : Value V} {w : Value W}
  → 𝒱 `ℕ ρ V W v w
  → 𝒱 `ℕ σ V W v w
𝒱-Nat-irrel {V = `zero} {W = `zero} {v = vZero} {w = vZero} VW-rel = tt
𝒱-Nat-irrel {V = `suc V} {W = `suc W} {v = vSuc v} {w = vSuc w} VW-rel =
  𝒱-Nat-irrel {V = V} {W = W} {v = v} {w = w} VW-rel

𝒱-Bool-irrel : ∀ {ρ σ V W} {v : Value V} {w : Value W}
  → 𝒱 `Bool ρ V W v w
  → 𝒱 `Bool σ V W v w
𝒱-Bool-irrel {V = `true} {W = `true} {v = vTrue} {w = vTrue} VW-rel = tt
𝒱-Bool-irrel {V = `false} {W = `false} {v = vFalse} {w = vFalse} VW-rel = tt

mutual
  𝒱-rename-wk :
    ∀ {A ξ ρ ρ' V W} {v : Value V} {w : Value W}
    → WkRel ξ ρ ρ'
    → 𝒱 A ρ V W v w
    → 𝒱 (renameᵗ ξ A) ρ' V W v w
  𝒱-rename-wk {A = ` α} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r ⟨ ⊢V , ⟨ ⊢W , rel ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ V ⦂ T) (wk-left-var wk-r α) ⊢V
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ W ⦂ T) (wk-right-var wk-r α) ⊢W
      , wk-ρR-cast {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r α {V = V} {W = W} {v = v} {w = w} {⊢V = ⊢V} {⊢W = ⊢W} rel
      ⟩ ⟩
  𝒱-rename-wk {A = `ℕ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    𝒱-Nat-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-rename-wk {A = `Bool} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    𝒱-Bool-irrel {ρ = ρ} {σ = ρ'} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-rename-wk {A = A ⇒ B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = ƛ[ C ] N} {W = ƛ[ D ] M} {v = vLam} {w = vLam} wk-r ⟨ ⊢V , ⟨ ⊢W , f-rel ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ (ƛ[ C ] N) ⦂ T) (sym (wk-left-subst wk-r (A ⇒ B))) ⊢V
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ (ƛ[ D ] M) ⦂ T) (sym (wk-right-subst wk-r (A ⇒ B))) ⊢W
      , (λ v₁ w₁ arg-rel' →
      ℰ-rename-wk {A = B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
        (f-rel v₁ w₁
          (𝒱-unrename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {v = v₁} {w = w₁} wk-r arg-rel'))
      ) ⟩ ⟩
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
  𝒱-rename-wk {A = `∀ A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam} wk-r ⟨ ⊢V , ⟨ ⊢W , ∀-rel ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ (Λ N) ⦂ T) (sym (wk-left-subst wk-r (`∀ A))) ⊢V
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ (Λ M) ⦂ T) (sym (wk-right-subst wk-r (`∀ A))) ⊢W
      , (λ A₁ A₂ wfA₁ wfA₂ R →
      ℰ-rename-wk
        {A = A}
        {ξ = extᵗ ξ}
        {ρ = ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩}
        {ρ' = ρ' ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩}
        (wk-ext
          {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂}
          wfA₁ wfA₂ R wk-r)
        (∀-rel A₁ A₂ wfA₁ wfA₂ R)
      ) ⟩ ⟩
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
  𝒱-unrename-wk {A = ` α} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r ⟨ ⊢V , ⟨ ⊢W , rel ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ V ⦂ T) (sym (wk-left-var wk-r α)) ⊢V
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ W ⦂ T) (sym (wk-right-var wk-r α)) ⊢W
      , wk-ρR-uncast {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r α {V = V} {W = W} {v = v} {w = w} {⊢V = ⊢V} {⊢W = ⊢W} rel
      ⟩ ⟩
  𝒱-unrename-wk {A = `ℕ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    𝒱-Nat-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-unrename-wk {A = `Bool} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW =
    𝒱-Bool-irrel {ρ = ρ'} {σ = ρ} {V = V} {W = W} {v = v} {w = w} 𝒱VW
  𝒱-unrename-wk {A = A ⇒ B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = ƛ[ C ] N} {W = ƛ[ D ] M} {v = vLam} {w = vLam} wk-r ⟨ ⊢V , ⟨ ⊢W , f-rel ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ (ƛ[ C ] N) ⦂ T) (wk-left-subst wk-r (A ⇒ B)) ⊢V
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ (ƛ[ D ] M) ⦂ T) (wk-right-subst wk-r (A ⇒ B)) ⊢W
      , (λ v₁ w₁ arg-rel →
      ℰ-unrename-wk {A = B} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} wk-r
        (f-rel v₁ w₁
          (𝒱-rename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {v = v₁} {w = w₁} wk-r arg-rel))
      ) ⟩ ⟩
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
  𝒱-unrename-wk {A = `∀ A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam} wk-r ⟨ ⊢V , ⟨ ⊢W , ∀-rel ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ (Λ N) ⦂ T) (wk-left-subst wk-r (`∀ A)) ⊢V
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ (Λ M) ⦂ T) (wk-right-subst wk-r (`∀ A)) ⊢W
      , (λ A₁ A₂ wfA₁ wfA₂ R →
      ℰ-unrename-wk
        {A = A}
        {ξ = extᵗ ξ}
        {ρ = ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩}
        {ρ' = ρ' ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩}
        (wk-ext
          {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {B₁ = A₁} {B₂ = A₂}
          wfA₁ wfA₂ R wk-r)
        (∀-rel A₁ A₂ wfA₁ wfA₂ R)
      ) ⟩ ⟩
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
  ℰ-rename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {M = M} {N = N} wk-r
    ⟨ ⊢M , ⟨ ⊢N , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ M ⦂ T) (sym (wk-left-subst wk-r A)) ⊢M
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ N ⦂ T) (sym (wk-right-subst wk-r A)) ⊢N
      , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W
        , 𝒱-rename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW
        ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

  ℰ-unrename-wk :
    ∀ {A ξ ρ ρ' M N}
    → WkRel ξ ρ ρ'
    → ℰ (renameᵗ ξ A) ρ' M N
    → ℰ A ρ M N
  ℰ-unrename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {M = M} {N = N} wk-r
    ⟨ ⊢M , ⟨ ⊢N , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ M ⦂ T) (wk-left-subst wk-r A) ⊢M
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ N ⦂ T) (wk-right-subst wk-r A) ⊢N
      , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W
        , 𝒱-unrename-wk {A = A} {ξ = ξ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} wk-r 𝒱VW
        ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

⇑-ℰ : ∀{A A₁ A₂}{ρ : RelSub}{γ : RelEnv}
    {wfA₁ : WfTy 0 A₁}{wfA₂ : WfTy 0 A₂}{R : Rel A₁ A₂}
  → ℰ A ρ (RelEnv.left γ 0) (RelEnv.right γ 0)
  → ℰ (renameᵗ suc A) (ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩) (RelEnv.left γ 0) (RelEnv.right γ 0)
⇑-ℰ {A}{A₁}{A₂}{ρ}{γ}{wfA₁}{wfA₂}{R} rel =
  ℰ-rename-wk {A = A} {ξ = suc} {ρ = ρ} {ρ' = ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩}
    (wk-suc wfA₁ wfA₂ R)
    rel

liftRelEnv-related : ∀ {Γ A₁ A₂} {ρ : RelSub} {γ : RelEnv}
    (wfA₁ : WfTy 0 A₁) (wfA₂ : WfTy 0 A₂)
    (R : Rel A₁ A₂)
  → 𝒢 Γ ρ γ
  → 𝒢 (⤊ Γ) (ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩) γ
liftRelEnv-related {[]} wfA₁ wfA₂ R G = tt
liftRelEnv-related {A ∷ Γ} {A₁ = A₁} {A₂ = A₂} {ρ} {γ} wfA₁ wfA₂ R G =
  ⟨ ⇑-ℰ {A = A} {A₁ = A₁} {A₂ = A₂} {ρ = ρ} {γ = γ} {wfA₁ = wfA₁} {wfA₂ = wfA₂} {R = R} (G .proj₁)
  , liftRelEnv-related {Γ} {A₁ = A₁} {A₂ = A₂} {ρ = ρ} {γ = ⇓γ γ} wfA₁ wfA₂ R (G .proj₂)
  ⟩

--------------------------------------------------------------------------------
-- Substituting type variables in the logical relation
--------------------------------------------------------------------------------

record SubstRel (σ : Substᵗ) (ρ : RelSub) (ρ' : RelSub) : Setω where
  field
    left-subst-var : (α : Var) → RelSub.left ρ' α ≡ᵗ substᵗ (RelSub.left ρ) (σ α)
    right-subst-var : (α : Var) → RelSub.right ρ' α ≡ᵗ substᵗ (RelSub.right ρ) (σ α)

    var⇒ : ∀ α {V W} {v : Value V} {w : Value W}
      → 𝒱 (` α) ρ' V W v w
      → 𝒱 (σ α) ρ V W v w

    var⇐ : ∀ α {V W} {v : Value V} {w : Value W}
      → 𝒱 (σ α) ρ V W v w
      → 𝒱 (` α) ρ' V W v w

exts-SubstRel : ∀ {σ ρ ρ' A₁ A₂}
  → (wfA₁ : WfTy 0 A₁) (wfA₂ : WfTy 0 A₂)
  → (R : Rel A₁ A₂)
  → SubstRel σ ρ ρ'
  → SubstRel (extsᵗ σ)
      (ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩)
      (ρ' ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩)
SubstRel.left-subst-var (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} wfA₁ wfA₂ R sr) 0 = refl
SubstRel.left-subst-var (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} wfA₁ wfA₂ R sr) (suc α) =
  trans
    (SubstRel.left-subst-var sr α)
    (sym (TS.rename-subst-commute suc (A₁ •ᵗ left ρ) (σ α)))

SubstRel.right-subst-var (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} wfA₁ wfA₂ R sr) 0 = refl
SubstRel.right-subst-var (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} wfA₁ wfA₂ R sr) (suc α) =
  trans
    (SubstRel.right-subst-var sr α)
    (sym (TS.rename-subst-commute suc (A₂ •ᵗ right ρ) (σ α)))

SubstRel.var⇒ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} wfA₁ wfA₂ R sr) 0 rel = rel
SubstRel.var⇒ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} wfA₁ wfA₂ R sr) (suc α) rel =
  𝒱-rename-wk {A = σ α} {ξ = suc} {ρ = ρ} {ρ' = ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩}
    (wk-suc {ρ = ρ} {A₁ = A₁} {A₂ = A₂} wfA₁ wfA₂ R)
    (SubstRel.var⇒ sr α rel)

SubstRel.var⇐ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} wfA₁ wfA₂ R sr) 0 rel = rel
SubstRel.var⇐ (exts-SubstRel {σ = σ} {ρ = ρ} {ρ' = ρ'} {A₁ = A₁} {A₂ = A₂} wfA₁ wfA₂ R sr) (suc α) rel =
  SubstRel.var⇐ sr α
    (𝒱-unrename-wk {A = σ α} {ξ = suc} {ρ = ρ} {ρ' = ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩}
      (wk-suc {ρ = ρ} {A₁ = A₁} {A₂ = A₂} wfA₁ wfA₂ R)
      rel)

substRel-left-subst : ∀ {σ ρ ρ'} (sr : SubstRel σ ρ ρ') (A : Ty)
  → substᵗ (RelSub.left ρ') A ≡ substᵗ (RelSub.left ρ) (substᵗ σ A)
substRel-left-subst {σ = σ} {ρ = ρ} {ρ' = ρ'} sr A =
  trans
    (TS.subst-cong (SubstRel.left-subst-var sr) A)
    (sym (TS.sub-sub σ (RelSub.left ρ) A))

substRel-right-subst : ∀ {σ ρ ρ'} (sr : SubstRel σ ρ ρ') (A : Ty)
  → substᵗ (RelSub.right ρ') A ≡ substᵗ (RelSub.right ρ) (substᵗ σ A)
substRel-right-subst {σ = σ} {ρ = ρ} {ρ' = ρ'} sr A =
  trans
    (TS.subst-cong (SubstRel.right-subst-var sr) A)
    (sym (TS.sub-sub σ (RelSub.right ρ) A))

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
  𝒱-subst {A = A ⇒ B} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = ƛ[ C ] N} {W = ƛ[ D ] M} {v = vLam} {w = vLam} sr ⟨ ⊢V , ⟨ ⊢W , f-rel ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ (ƛ[ C ] N) ⦂ T) (substRel-left-subst sr (A ⇒ B)) ⊢V
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ (ƛ[ D ] M) ⦂ T) (substRel-right-subst sr (A ⇒ B)) ⊢W
      , (λ v₁ w₁ arg-rel →
      ℰ-subst {A = B} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
        (f-rel v₁ w₁ (𝒱-unsubst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {v = v₁} {w = w₁} sr arg-rel))
      ) ⟩ ⟩
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
  𝒱-subst {A = `∀ A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam} sr ⟨ ⊢V , ⟨ ⊢W , ∀-rel ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ (Λ N) ⦂ T) (substRel-left-subst sr (`∀ A)) ⊢V
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ (Λ M) ⦂ T) (substRel-right-subst sr (`∀ A)) ⊢W
      , (λ A₁ A₂ wfA₁ wfA₂ R →
      ℰ-subst {A = A} {σ = extsᵗ σ}
        {ρ = ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩}
        {ρ' = ρ' ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩}
        (exts-SubstRel wfA₁ wfA₂ R sr)
        (∀-rel A₁ A₂ wfA₁ wfA₂ R)
      ) ⟩ ⟩
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
  𝒱-unsubst {A = A ⇒ B} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = ƛ[ C ] N} {W = ƛ[ D ] M} {v = vLam} {w = vLam} sr ⟨ ⊢V , ⟨ ⊢W , f-rel ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ (ƛ[ C ] N) ⦂ T) (sym (substRel-left-subst sr (A ⇒ B))) ⊢V
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ (ƛ[ D ] M) ⦂ T) (sym (substRel-right-subst sr (A ⇒ B))) ⊢W
      , (λ v₁ w₁ arg-rel →
      ℰ-unsubst {A = B} {σ = σ} {ρ = ρ} {ρ' = ρ'} sr
        (f-rel v₁ w₁ (𝒱-subst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {v = v₁} {w = w₁} sr arg-rel))
      ) ⟩ ⟩
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
  𝒱-unsubst {A = `∀ A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = Λ N} {W = Λ M} {v = vTlam} {w = vTlam} sr ⟨ ⊢V , ⟨ ⊢W , ∀-rel ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ (Λ N) ⦂ T) (sym (substRel-left-subst sr (`∀ A))) ⊢V
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ (Λ M) ⦂ T) (sym (substRel-right-subst sr (`∀ A))) ⊢W
      , (λ A₁ A₂ wfA₁ wfA₂ R →
      ℰ-unsubst {A = A} {σ = extsᵗ σ}
        {ρ = ρ ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩}
        {ρ' = ρ' ,⟨ A₁ , A₂ , wfA₁ , wfA₂ , R ⟩}
        (exts-SubstRel wfA₁ wfA₂ R sr)
        (∀-rel A₁ A₂ wfA₁ wfA₂ R)
      ) ⟩ ⟩
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
  ℰ-subst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {M = M} {N = N} sr
    ⟨ ⊢M , ⟨ ⊢N , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ M ⦂ T) (substRel-left-subst sr A) ⊢M
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ N ⦂ T) (substRel-right-subst sr A) ⊢N
      , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W
        , 𝒱-subst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW
        ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

  ℰ-unsubst :
    ∀ {A σ ρ ρ' M N}
    → SubstRel σ ρ ρ'
    → ℰ (substᵗ σ A) ρ M N
    → ℰ A ρ' M N
  ℰ-unsubst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {M = M} {N = N} sr
    ⟨ ⊢M , ⟨ ⊢N , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W , 𝒱VW ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ substEq (λ T → 0 ∣ [] ⊢ M ⦂ T) (sym (substRel-left-subst sr A)) ⊢M
    , ⟨ substEq (λ T → 0 ∣ [] ⊢ N ⦂ T) (sym (substRel-right-subst sr A)) ⊢N
      , ⟨ V , ⟨ W , ⟨ v , ⟨ w , ⟨ M—↠V , ⟨ N—↠W
        , 𝒱-unsubst {A = A} {σ = σ} {ρ = ρ} {ρ' = ρ'} {V = V} {W = W} {v = v} {w = w} sr 𝒱VW
        ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

singleTy-SubstRel : ∀ {ρ B}
  → SubstRel (singleTyEnv B) ρ
      (ρ ,⟨ substᵗ (left ρ) B
           , substᵗ (right ρ) B
           , substᵗ-codom-closed (left ρ) (left-closed ρ) B
           , substᵗ-codom-closed (right ρ) (right-closed ρ) B
           , (λ V W v w ⊢V ⊢W → 𝒱 B ρ V W v w) ⟩)
SubstRel.left-subst-var (singleTy-SubstRel {ρ = ρ} {B = B}) 0 = refl
SubstRel.left-subst-var (singleTy-SubstRel {ρ = ρ} {B = B}) (suc α) = refl
SubstRel.right-subst-var (singleTy-SubstRel {ρ = ρ} {B = B}) 0 = refl
SubstRel.right-subst-var (singleTy-SubstRel {ρ = ρ} {B = B}) (suc α) = refl
SubstRel.var⇒ (singleTy-SubstRel {ρ = ρ} {B = B}) 0 ⟨ ⊢V , ⟨ ⊢W , relB ⟩ ⟩ = relB
SubstRel.var⇒ (singleTy-SubstRel {ρ = ρ} {B = B}) (suc α) rel = rel
SubstRel.var⇐ (singleTy-SubstRel {ρ = ρ} {B = B}) 0 {V = V} {W = W} {v = v} {w = w} relB
  with 𝒱-typing {A = B} {ρ = ρ} {V = V} {W = W} {v = v} {w = w} relB
... | ⟨ ⊢V , ⊢W ⟩ = ⟨ ⊢V , ⟨ ⊢W , relB ⟩ ⟩
SubstRel.var⇐ (singleTy-SubstRel {ρ = ρ} {B = B}) (suc α) rel = rel

𝒱-compositionality⇒ : ∀ {A B ρ V W} {v : Value V} {w : Value W}
  → 𝒱 A (ρ ,⟨ substᵗ (left ρ) B
             , substᵗ (right ρ) B
             , substᵗ-codom-closed (left ρ) (left-closed ρ) B
             , substᵗ-codom-closed (right ρ) (right-closed ρ) B
             , (λ V W v w ⊢V ⊢W → 𝒱 B ρ V W v w) ⟩) V W v w
  → 𝒱 (A [ B ]ᵗ) ρ V W v w
𝒱-compositionality⇒ {A = A} {B = B} {ρ = ρ} {V = V} {W = W} {v = v} {w = w} 𝒱VW =
  𝒱-subst {A = A} {σ = singleTyEnv B} {ρ = ρ}
    {ρ' = ρ ,⟨ substᵗ (left ρ) B
              , substᵗ (right ρ) B
              , substᵗ-codom-closed (left ρ) (left-closed ρ) B
              , substᵗ-codom-closed (right ρ) (right-closed ρ) B
              , (λ V W v w ⊢V ⊢W → 𝒱 B ρ V W v w) ⟩}
    {V = V} {W = W} {v = v} {w = w}
    singleTy-SubstRel 𝒱VW

𝒱-compositionality⇐ : ∀ {A B ρ V W} {v : Value V} {w : Value W}
  → 𝒱 (A [ B ]ᵗ) ρ V W v w
  → 𝒱 A (ρ ,⟨ substᵗ (left ρ) B
             , substᵗ (right ρ) B
             , substᵗ-codom-closed (left ρ) (left-closed ρ) B
             , substᵗ-codom-closed (right ρ) (right-closed ρ) B
             , (λ V W v w ⊢V ⊢W → 𝒱 B ρ V W v w) ⟩) V W v w
𝒱-compositionality⇐ {A = A} {B = B} {ρ = ρ} {V = V} {W = W} {v = v} {w = w} 𝒱VW =
  𝒱-unsubst {A = A} {σ = singleTyEnv B} {ρ = ρ}
    {ρ' = ρ ,⟨ substᵗ (left ρ) B
              , substᵗ (right ρ) B
              , substᵗ-codom-closed (left ρ) (left-closed ρ) B
              , substᵗ-codom-closed (right ρ) (right-closed ρ) B
              , (λ V W v w ⊢V ⊢W → 𝒱 B ρ V W v w) ⟩}
    {V = V} {W = W} {v = v} {w = w}
    singleTy-SubstRel 𝒱VW

ℰ-compositionality⇒ : ∀ {A B ρ M N}
  → ℰ A (ρ ,⟨ substᵗ (left ρ) B
             , substᵗ (right ρ) B
             , substᵗ-codom-closed (left ρ) (left-closed ρ) B
             , substᵗ-codom-closed (right ρ) (right-closed ρ) B
             , (λ V W v w ⊢V ⊢W → 𝒱 B ρ V W v w) ⟩) M N
  → ℰ (A [ B ]ᵗ) ρ M N
ℰ-compositionality⇒ {A = A} {B = B} {ρ = ρ} {M = M} {N = N} relMN =
  ℰ-subst {A = A} {σ = singleTyEnv B} {ρ = ρ}
    {ρ' = ρ ,⟨ substᵗ (left ρ) B
              , substᵗ (right ρ) B
              , substᵗ-codom-closed (left ρ) (left-closed ρ) B
              , substᵗ-codom-closed (right ρ) (right-closed ρ) B
              , (λ V W v w ⊢V ⊢W → 𝒱 B ρ V W v w) ⟩}
    singleTy-SubstRel relMN

ℰ-compositionality⇐ : ∀ {A B ρ M N}
  → ℰ (A [ B ]ᵗ) ρ M N
  → ℰ A (ρ ,⟨ substᵗ (left ρ) B
             , substᵗ (right ρ) B
             , substᵗ-codom-closed (left ρ) (left-closed ρ) B
             , substᵗ-codom-closed (right ρ) (right-closed ρ) B
             , (λ V W v w ⊢V ⊢W → 𝒱 B ρ V W v w) ⟩) M N
ℰ-compositionality⇐ {A = A} {B = B} {ρ = ρ} {M = M} {N = N} relMN =
  ℰ-unsubst {A = A} {σ = singleTyEnv B} {ρ = ρ}
    {ρ' = ρ ,⟨ substᵗ (left ρ) B
              , substᵗ (right ρ) B
              , substᵗ-codom-closed (left ρ) (left-closed ρ) B
              , substᵗ-codom-closed (right ρ) (right-closed ρ) B
              , (λ V W v w ⊢V ⊢W → 𝒱 B ρ V W v w) ⟩}
    singleTy-SubstRel relMN
