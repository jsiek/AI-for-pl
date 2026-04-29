{-# OPTIONS --cumulativity --omega-in-omega #-}
module curry.proof.LogicalRelation where

-- File Charter:
--   * Contains proof-only logical-relation infrastructure for curry System F.
--   * Proves renaming/substitution transport lemmas and lifted related-environment lemmas.
--   * Keeps these internals out of the public `curry.LogicalRelation` surface.

open import Data.List using (_∷_; [])
open import Data.Nat using (zero; suc)
open import curry.ProductOmega using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Level using (Setω)

open import curry.Types
open import curry.Terms
open import curry.Reduction
open import curry.LogicalRelation

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
