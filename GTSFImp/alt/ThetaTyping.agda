module alt.ThetaTyping where

-- File Charter:
--   * Defines typing for the Θ-indexed alternative syntax.  The binder
--     telescope `TyEnv` holds type-variable entries (with their recorded
--     insertion position) and anchor:=representation entries; term
--     variables live in a separate `TermCtx` list, so a context with no
--     term variables is the literal `[]` — closed interiors for ν and
--     the crossings are structural, with no erasure.
--   * Representations are written in the regular scope at their entry;
--     the anchor lookup performs the spelling, weakening entries across
--     later type-variable insertions (skip-typ).  Anchors never occur in
--     regular types `Ty Δ`.
--   * Term variables cross only Λ's type-variable entry, by weakening the
--     term list wholesale (renameCtx), as in the live calculus.

open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)

open import Types
open import TermCtx
open import Primitives
open import Consistency
open import alt.ThetaTerms
open import alt.Conversion

private
  variable
    Θ Θ′ : AnchorCtx
    Δ : TyCtx

------------------------------------------------------------------------
-- Binder telescopes: type variables and anchors, no term variables
------------------------------------------------------------------------

infixl 5 _,typ[_]
infixl 5 _,:=_

data TyEnv : AnchorCtx → TyCtx → Set where
  ∅ : TyEnv zero zero
  _,typ[_] : TyEnv Θ Δ → TyVar (suc Δ) → TyEnv Θ (suc Δ)
  _,:=_ : TyEnv Θ Δ → Ty Δ → TyEnv (suc Θ) Δ  -- anchor bound by a ν

private
  variable
    Ψ Ψ′ : TyEnv Θ Δ
    Γ Γ′ : TermCtx Δ
    A B C : Ty Δ
    x y z : Var
    a b : TyVar Θ

infix 4 _∋_:=_

data _∋_:=_ : ∀ {Θ Δ} → TyEnv Θ Δ → TyVar Θ → Ty Δ → Set where
  Z :
      ---------------------
      (Ψ ,:= A) ∋ zero := A

  S :
      Ψ ∋ a := A
      ----------------------
    → (Ψ ,:= B) ∋ suc a := A

  skip-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {a} {A : Ty Δ}
      {Y : TyVar (suc Δ)}
    → Ψ ∋ a := A
      -----------------------------
    → (Ψ ,typ[ Y ]) ∋ a := wkᵗ Y A

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

private
  variable
    L M N : Term Θ Δ

infix 4 _∣_⊢_⦂_

data _∣_⊢_⦂_ : ∀ {Θ Δ}
  → TyEnv Θ Δ → TermCtx Δ → Term Θ Δ → Ty Δ → Set where
  ⊢` :
      Γ ∋ x ⦂ A
      -------------------
    → Ψ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ :
      Ψ ∣ A ∷ Γ ⊢ M ⦂ B
      -----------------------------
    → Ψ ∣ Γ ⊢ (ƛ A ˙ M) ⦂ (A ⇒ B)

  ⊢· :
      Ψ ∣ Γ ⊢ L ⦂ (A ⇒ B)
    → Ψ ∣ Γ ⊢ M ⦂ A
      ---------------------
    → Ψ ∣ Γ ⊢ (L · M) ⦂ B

  -- DEFERRED: value restriction
  ⊢Λ :
      Ψ ,typ[ zero ] ∣ renameCtx suc Γ ⊢ M ⦂ A
      -----------------------------------------
    → Ψ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢⦂∀ :
      Ψ ∣ Γ ⊢ L ⦂ `∀ C
      ----------------------------------
    → Ψ ∣ Γ ⊢ L ⦂∀ C [ A ] ⦂ C [ A ]ᵗ

  ⊢$ : ∀ (κ : Const)
      ---------------------------
    → Ψ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ :
      (op : Prim)
    → Ψ ∣ Γ ⊢ L ⦂ primArgTy op
    → Ψ ∣ Γ ⊢ M ⦂ primArgTy op
      -------------------------------------------
    → Ψ ∣ Γ ⊢ (L ⊕[ op ] M) ⦂ primResultTy op

  ⊢⟨⟩ : ∀ {μ}
    → Ψ ∣ Γ ⊢ M ⦂ A
    → (c : μ ⊢ A ∼ B)
      ---------------------
    → Ψ ∣ Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢ν :
      Ψ ,:= A ∣ [] ⊢ M ⦂ B
      ----------------------
    → Ψ ∣ Γ ⊢ ν[ A ] M ⦂ B

  ⊢reveal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ : TermCtx Δ}
      {M : Term Θ (suc Δ)}
      {A : Ty (suc Δ)} {B C : Ty Δ} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal}
    → Ψ ∋ α := C
    → ⊢↑[ Y ⦂ wkᵗ Y C ] c ⦂ A ↝ wkᵗ Y B
    → Ψ ,typ[ Y ] ∣ [] ⊢ M ⦂ A
      --------------------------------
    → Ψ ∣ Γ ⊢ M ↑[ Y ≔ α ] c ⦂ B

  ⊢conceal : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ′ : TermCtx (suc Δ)}
      {M : Term Θ Δ}
      {A C : Ty Δ} {B : Ty (suc Δ)} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
    → Ψ ∋ α := C
    → ⊢↓[ Y ⦂ wkᵗ Y C ] c ⦂ wkᵗ Y A ↝ B
    → Ψ ∣ [] ⊢ M ⦂ A
      ------------------------------------------
    → Ψ ,typ[ Y ] ∣ Γ′ ⊢ M ↓[ Y ≔ α ] c ⦂ B

  ⊢blame :
      ---------------------
      Ψ ∣ Γ ⊢ blame ⦂ A
