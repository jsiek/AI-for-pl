module alt.Terms where

-- File Charter:
--   * Reveal/conceal bind and anti-bind type variables (Δ context).
--   * There is no ν construct.

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import Primitives
open import Consistency

private
  variable
    Δ : TyCtx

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_˙_
infixl 7 _·_
infix  5 Λ_
infixl 7 _⦂∀_[_]
infixl 7 _⟨_⟩
infixl 7 _↑[_] _↓[_]
infixl 6 _⊕[_]_
infix  9 `_

Var : Set
Var = ℕ

data Term : TyCtx → Set where
  `_      : Var → Term Δ
  ƛ_˙_    : Ty Δ → Term Δ → Term Δ
  _·_     : Term Δ → Term Δ → Term Δ
  Λ_      : Term (suc Δ) → Term Δ
  _⦂∀_[_] : Term Δ → Ty (suc Δ) → Ty Δ → Term Δ
  $       : Const → Term Δ
  _⊕[_]_  : Term Δ → Prim → Term Δ → Term Δ
  _⟨_⟩    : Term Δ → {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Term Δ

  _↑[_] : Term (suc Δ) → Ty Δ → Term Δ

  -- conceal: the body lives in the unwound context (Δ′), the wrapper in the
  -- context at the conceal point (suc Δ).  The relationship between Δ′ and suc Δ
  -- is fixed by the unwind relation (_,end[_]↝_) in the ⊢conceal rule.
  _↓[_] : ∀ {Δ Δ′} → Term Δ′ → TyVar (suc Δ) → Term (suc Δ)

  blame : Term Δ


------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

infixl 5 _,begin[_] _,typ

-- A type environment is a push-only stack of reveal binders (,begin[_]) and
-- type abstractions (,typ).  Concealment is not a frame: it unwinds the stack
-- (see _,end[_]↝_ below), popping back to the context in which the matching
-- ,begin[_] happened.
data TyEnv : (Δ : TyCtx) → Set where
  ∅ : TyEnv zero

  _,begin[_] :
      TyEnv Δ
    → Ty Δ
    → TyEnv (suc Δ)

  _,typ :
      TyEnv Δ
    → TyEnv (suc Δ)

infix 4 _∋_:=_

data _∋_:=_ : ∀ {Δ : TyCtx} → TyEnv (suc Δ) → TyVar (suc Δ) → Ty Δ → Set where
  Z : ∀ {Δ} {Ψ : TyEnv Δ} {A : Ty Δ}
      ---------------------------
    → (Ψ ,begin[ A ]) ∋ zero := A

  -- Skip past a reveal binder (,begin[_]).
  Sb : ∀ {Δ} {Ψ : TyEnv (suc Δ)} {A : Ty Δ} {B : Ty (suc Δ)}
      {x : TyVar (suc Δ)}
    → Ψ ∋ x := A
      -------------------------------
    → (Ψ ,begin[ B ]) ∋ suc x := ⇑ᵗ A

  -- Skip past a type abstraction (,typ): the abstract variable itself has no
  -- representation, so a deeper representation is simply weakened.
  St : ∀ {Δ} {Ψ : TyEnv (suc Δ)} {A : Ty Δ} {x : TyVar (suc Δ)}
    → Ψ ∋ x := A
      -------------------------------
    → (Ψ ,typ) ∋ suc x := ⇑ᵗ A

------------------------------------------------------------------------
-- Concealment as stack unwinding
------------------------------------------------------------------------

-- (Ψ ,end[ X ]↝ Ψ′) means: concealing the reveal variable X pops the stack Ψ
-- back to Ψ′, the context in which X's matching ,begin[_] happened.  Everything
-- pushed after that ,begin[_] (including any ,typ abstractions) is dropped, so
-- those variables are no longer in scope.  There is deliberately no clause for
-- concealing a ,typ-bound variable (an abstraction variable cannot be
-- concealed), so that case fails.
--
-- Consequently lookup is transparent across a matched bracket:
--   (Ψ ,begin[ A ] .... ,end[ X ]) unwinds to Ψ, hence
--   the concealed body is looked up directly in Ψ.
infix 4 _,end[_]↝_

data _,end[_]↝_ : ∀ {Δ Δ′} → TyEnv Δ → TyVar Δ → TyEnv Δ′ → Set where
  -- Reached the matching begin: pop it, revealing the context below.
  here : ∀ {Δ} {Ψ : TyEnv Δ} {A : Ty Δ}
      ---------------------------
    → (Ψ ,begin[ A ]) ,end[ zero ]↝ Ψ

  -- Pop a more-recent type abstraction and keep unwinding.  (There is no clause
  -- for a more-recent reveal binder: by the LIFO discipline any reveal opened
  -- after Y is concealed before Y, so no open ,begin[_] sits above Y here.)
  pop-t : ∀ {Δ Δ′} {Ψ : TyEnv (suc Δ)} {Ψ′ : TyEnv Δ′}
      {Y : TyVar (suc Δ)}
    → Ψ ,end[ Y ]↝ Ψ′
      -------------------------------
    → (Ψ ,typ) ,end[ suc Y ]↝ Ψ′

-- The substitution induced by concealing Y: it maps the context at the conceal
-- point (suc Δ) down to the unwound context (Δ′).  The concealed variable goes
-- to its representation (singleSubᵗ, generalising the old A [ B ]ᵗ), and each
-- popped ,typ abstraction variable is strengthened away (mapped to ★, which is
-- sound provided it does not occur in the concealed type).
endSub : ∀ {Δ Δ′} {Ψ : TyEnv (suc Δ)} {Ψ′ : TyEnv Δ′}
    {Y : TyVar (suc Δ)} {B : Ty Δ}
  → Ψ ∋ Y := B
  → Ψ ,end[ Y ]↝ Ψ′
  → (suc Δ) ⇒ˢ Δ′
endSub (Z {A = A}) here = singleSubᵗ A
endSub (St ℓ) (pop-t u) = λ where
    zero    → ★
    (suc i) → endSub ℓ u i
endSub (Sb _) ()



data TermCtx (Δ : TyCtx) : Set where
  [] : TermCtx Δ
  _∷_ : Ty Δ → TermCtx Δ → TermCtx Δ

infix 4 _∋_⦂_

data _∋_⦂_ {Δ : TyCtx} : TermCtx Δ → ℕ → Ty Δ → Set where
  Z : ∀ {Γ A}
      -----------------
    → (A ∷ Γ) ∋ zero ⦂ A

  S : ∀ {Γ A B x}
    → Γ ∋ x ⦂ A
      -------------------
    → (B ∷ Γ) ∋ suc x ⦂ A

renameCtx : ∀ {Δ Δ′} → Δ ⇒ʳ Δ′ → TermCtx Δ → TermCtx Δ′
renameCtx ρ [] = []
renameCtx ρ (A ∷ Γ) = renameᵗ ρ A ∷ renameCtx ρ Γ

⇑ᶜ : ∀ {Δ} → TermCtx Δ → TermCtx (suc Δ)
⇑ᶜ = renameCtx suc

private
  variable
    Ψ Ψ′ : TyEnv Δ
    Γ Γ′ : TermCtx Δ
    A B C : Ty Δ
    L M N : Term Δ
    x y z : Var

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

infix 4 _∣_⊢_⦂_

data _∣_⊢_⦂_ : ∀ {Δ}
  → (Ψ : TyEnv Δ) → TermCtx Δ → Term Δ → Ty Δ → Set where
  ⊢` : ∀ {Δ} {Ψ : TyEnv Δ} {Γ : TermCtx Δ} {x : Var} {A : Ty Δ}
    → Γ ∋ x ⦂ A
      ---------------------------------------
    → Ψ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ :
      Ψ ∣ A ∷ Γ ⊢ M ⦂ B
      ----------------------------
    → Ψ ∣ Γ ⊢ (ƛ A ˙ M) ⦂ (A ⇒ B)

  ⊢· :
      Ψ ∣ Γ ⊢ L ⦂ (A ⇒ B)
    → Ψ ∣ Γ ⊢ M ⦂ A
      ---------------------
    → Ψ ∣ Γ ⊢ (L · M) ⦂ B

  ⊢Λ :
      Ψ ,typ ∣ ⇑ᶜ Γ ⊢ M ⦂ A
      -------------------------
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

  ⊢reveal : ∀ {Δ} {Ψ : TyEnv Δ} {Γ : TermCtx Δ}
      {M : Term (suc Δ)}
      {A : Ty (suc Δ)} {B : Ty Δ} 
    → Ψ ,begin[ B ] ∣ ⇑ᶜ Γ ⊢ M ⦂ A
      -----------------------------
    → Ψ ∣ Γ ⊢ M ↑[ B ] ⦂ A [ B ]ᵗ

  -- Conceal Y: unwind the type environment past Y's matching ,begin[_] to Ψ′
  -- and type the body M there.  The body's type is the result type A pushed
  -- down along the concealment substitution (endSub): Y is replaced by its
  -- representation and any popped ,typ abstractions are strengthened away.  When
  -- the unwind is single-level this is exactly the old A [ B ]ᵗ.
  ⊢conceal : ∀ {Δ Δ′} {Ψ : TyEnv (suc Δ)} {Ψ′ : TyEnv Δ′}
      {Γ : TermCtx (suc Δ)} {Γ′ : TermCtx Δ′}
      {M : Term Δ′} {A : Ty (suc Δ)} {B : Ty Δ} {Y : TyVar (suc Δ)}
    → (⊢Y : Ψ ∋ Y := B)
    → (u : Ψ ,end[ Y ]↝ Ψ′)
    → Ψ′ ∣ Γ′ ⊢ M ⦂ substᵗ (endSub ⊢Y u) A
      ------------------------------
    → Ψ ∣ Γ ⊢ M ↓[ Y ] ⦂ A

  ⊢blame :
      ---------------------
      Ψ ∣ Γ ⊢ blame ⦂ A
