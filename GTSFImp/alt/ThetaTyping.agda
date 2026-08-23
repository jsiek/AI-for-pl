module alt.ThetaTyping where

-- File Charter:
--   * Defines typing for the Θ-indexed alternative syntax.  Anchors index
--     telescopes and terms, but never occur in regular types `Ty Δ`.
--   * Defines the first-order classifier for exactly two semantic consumers:
--     the spelling premise used by crossings here, and allocation later.
--   * Makes `∀-bound` entries deliberately unspellable, preventing lexical
--     variables from being mistaken for anchor-backed representation slots.
--   * Enforces closed interiors for ν, wk, reveal, and conceal.

open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import Primitives
open import Consistency
open import alt.ThetaTerms
open import alt.Conversion

------------------------------------------------------------------------
-- Anchor telescopes
------------------------------------------------------------------------

private
  variable
    Θ Θ′ : AnchorCtx
    Δ : TyCtx

------------------------------------------------------------------------
-- Typing contexts
------------------------------------------------------------------------

infixl 5 _,typ[_]
infixl 5 _,_
infixl 5 _,:=_

data Ctx : AnchorCtx → TyCtx → Set where
  _,typ[_] : Ctx Θ Δ → TyVar (suc Δ) → Ctx Θ (suc Δ)
  _,_ : Ctx Θ Δ → Ty Δ → Ctx Θ Δ        -- term var. bound by a λ
  _,:=_ : Ctx Θ Δ → Ty Δ → Ctx (suc Θ) Δ  -- anchor var. bound by a ν

private
  variable
    Γ Γ′ : Ctx Θ Δ
    A B C : Ty Δ
    x y z : Var
    a b : TyVar Θ

infix 4 _∋_⦂_

data _∋_⦂_ : ∀ {Θ Δ} → Ctx Θ Δ → ℕ → Ty Δ → Set where
  Z :
      -----------------
     (Γ , A) ∋ zero ⦂ A

  S :
      Γ ∋ x ⦂ A
      -------------------
    → (Γ , B) ∋ suc x ⦂ A

  skip-rep :
      Γ ∋ x ⦂ A
      -------------------
    → (Γ ,:= B) ∋ x ⦂ A

  skip-typ : ∀ {Θ Δ} {Γ : Ctx Θ Δ} {x} {A : Ty Δ}
      {Y : TyVar (suc Δ)}
    → Γ ∋ x ⦂ A
      -------------------
    → (Γ ,typ[ Y ]) ∋ x ⦂ wkᵗ Y A


infix 4 _∋_:=_
data _∋_:=_ : ∀ {Θ Δ} → Ctx Θ Δ → TyVar Θ → Ty Δ → Set where
  Z :
      --------------------
     (Γ ,:= A) ∋ zero := A

  S :
      Γ ∋ a := A
      ----------------------
    → (Γ ,:= B) ∋ suc a := A

  skip-typ : ∀ {Θ Δ} {Γ : Ctx Θ Δ} {a} {A : Ty Δ}
      {Y : TyVar (suc Δ)}
    → Γ ∋ a := A
      -------------------
    → (Γ ,typ[ Y ]) ∋ a := wkᵗ Y A

  skip-trm :
      Γ ∋ a := A
      -------------------
    → (Γ , B) ∋ a := A

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

private
  variable
    L M N : Term Θ Δ

infix 4 _⊢_⦂_

data _⊢_⦂_ : ∀ {Θ Δ}
  → Ctx Θ Δ → Term Θ Δ → Ty Δ → Set where
  ⊢` :
      Γ ∋ x ⦂ A
      ---------------
    → Γ ⊢ (` x) ⦂ A

  ⊢ƛ :
      Γ , A ⊢ M ⦂ B
      -------------------------
    → Γ ⊢ (ƛ A ˙ M) ⦂ (A ⇒ B)

  ⊢· :
      Γ ⊢ L ⦂ (A ⇒ B)
    → Γ ⊢ M ⦂ A
      ------------------------------
    → Γ ⊢ (L · M) ⦂ B

--   -- DEFERRED: value restriction
  ⊢Λ :
      Γ ,typ[ zero ] ⊢ M ⦂ A
      ------------------
    → Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢⦂∀ :
      Γ ⊢ L ⦂ `∀ C
      -----------------------------
    → Γ ⊢ L ⦂∀ C [ A ] ⦂ C [ A ]ᵗ

  ⊢$ : ∀ (κ : Const)
      -----------------------
    → Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ :
      (op : Prim)
    → Γ ⊢ L ⦂ primArgTy op
    → Γ ⊢ M ⦂ primArgTy op
      -------------------------------------
    → Γ ⊢ (L ⊕[ op ] M) ⦂ primResultTy op

  ⊢⟨⟩ : ∀ {μ}
    → Γ ⊢ M ⦂ A
    → (c : μ ⊢ A ∼ B)
      -----------------
    → Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢ν :
      Γ ,:= A ⊢ M ⦂ B
      ----------------
    → Γ ⊢ ν[ A ] M ⦂ B

  ⊢reveal : ∀ {Θ Δ} {Γ : Ctx Θ Δ} {M : Term Θ (suc Δ)}
      {A : Ty (suc Δ)} {B C : Ty Δ} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal}
    → Γ ∋ α := C
    → ⊢↑[ Y ⦂ wkᵗ Y C ] c ⦂ A ↝ wkᵗ Y B
    → Γ ,typ[ Y ] ⊢ M ⦂ A
      --------------------------------------------
    → Γ ⊢ M ↑[ Y ≔ α ] c ⦂ B

  ⊢conceal : ∀ {Θ Δ} {Γ : Ctx Θ Δ} {M : Term Θ Δ}
      {A C : Ty Δ} {B : Ty (suc Δ)} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
    → Γ ∋ α := C
    → ⊢↓[ Y ⦂ wkᵗ Y C ] c ⦂ wkᵗ Y A ↝ B
    → Γ ⊢ M ⦂ A
      --------------------------------------------
    → Γ ,typ[ Y ] ⊢ M ↓[ Y ≔ α ] c ⦂ B

  ⊢blame :
      ---------------
      Γ ⊢ blame ⦂ A
