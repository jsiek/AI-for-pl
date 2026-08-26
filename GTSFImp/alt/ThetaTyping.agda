module alt.ThetaTyping where

-- File Charter:
--   * Defines typing for the Θ-indexed alternative syntax.  The binder
--     telescope `TyEnv` holds type-variable entries (with their recorded
--     insertion position) and anchor:=representation entries.  Term variables
--     live in a separate `TermCtx` list, so a context with no term variables
--     is the literal `[]` — closed interiors for ν and the crossings are
--     structural, with no erasure.
--   * Crossing-slot entries record both their insertion position and anchor.
--     Lexical Λ entries are separate: a lexical variable is always newest in
--     its prefix, and later prefix insertions are strictly older, so its
--     formerly constant position argument carried no information.
--   * A representation binding and every crossing of its anchor occur at the
--     same regular-context depth.  `_≼[_]_` recognizes the Δ-balanced segment
--     between birth and query; reduction-created re-entry pairs are its
--     `≼-end-begin` case at the same slot and shifted anchor.  Anchor lookup
--     therefore returns the birth-scope representation verbatim: no weakening,
--     resolution, or deferred payload syntax is involved.
--   * Term variables cross only Λ's type-variable entry, by weakening the
--     term list wholesale (renameCtx), as in the live calculus.

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

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

infixl 5 _,begin[_≔_] _,typ _,end[_]
infixl 5 _,:=_

data TyEnv : AnchorCtx → TyCtx → Set where
  ∅ : TyEnv zero zero
  _,begin[_≔_] : TyEnv Θ Δ → TyVar (suc Δ) → TyVar Θ
    → TyEnv Θ (suc Δ)
  _,typ : TyEnv Θ Δ → TyEnv Θ (suc Δ)
  _,:=_ : TyEnv Θ Δ → Ty Δ → TyEnv (suc Θ) Δ
  _,end[_] : TyEnv Θ (suc Δ) → TyVar (suc Δ) → TyEnv Θ Δ

private
  variable
    Ψ Ψ′ : TyEnv Θ Δ
    Γ Γ′ : TermCtx Δ
    A B C : Ty Δ
    x y z : Var
    a b : TyVar Θ

infix 4 _∋typ_≔_

-- Slot lookup: `Ψ ∋typ Y ≔ α` finds the begin entry that binds the
-- type variable Y in Ψ and returns its recorded anchor α.
data _∋typ_≔_ : TyEnv Θ Δ → TyVar Δ → TyVar Θ
    → Set where
  found-begin : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {Y : TyVar (suc Δ)} {α : TyVar Θ}
      ---------------------------------
    → (Ψ ,begin[ Y ≔ α ]) ∋typ Y ≔ α

  skip-begin : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {Y : TyVar Δ} {α : TyVar Θ}
      {X : TyVar (suc Δ)} {β : TyVar Θ}
    → Ψ ∋typ Y ≔ α
      -----------------------------------------------------
    → (Ψ ,begin[ X ≔ β ]) ∋typ punchIn X Y ≔ α

  skip-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {Y : TyVar Δ} {α : TyVar Θ}
    → Ψ ∋typ Y ≔ α
      -----------------------------
    → (Ψ ,typ) ∋typ (suc Y) ≔ α

  skip-nu-binding : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {Y : TyVar Δ} {α : TyVar Θ} {A : Ty Δ}
    → Ψ ∋typ Y ≔ α
      --------------------------------
    → (Ψ ,:= A) ∋typ Y ≔ suc α

  skip-end : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
      {Y : TyVar (suc Δ)} {X : TyVar Δ} {α : TyVar Θ}
    → Ψ ∋typ punchIn Y X ≔ α
      -------------------------------------------------
    → (Ψ ,end[ Y ]) ∋typ X ≔ α

------------------------------------------------------------------------
-- Balanced extension and verbatim representation lookup
------------------------------------------------------------------------

infix 4 _≼[_]_ _∋rep_≔_

-- `Shifted k α β` is the first-order bookkeeping for adding k newest
-- anchors.  Keeping Θ′ existential avoids associativity casts in telescope
-- indices; the evidence is unique and mirrors k leading `suc`s.
data Shifted : ∀ {Θ Θ′} → ℕ → TyVar Θ → TyVar Θ′ → Set where
  shifted-zero : ∀ {Θ} {α : TyVar Θ} → Shifted zero α α
  shifted-suc : ∀ {Θ Θ′ k} {α : TyVar Θ} {β : TyVar Θ′}
    → Shifted k α β
    → Shifted (suc k) α (suc β)

data _≼[_]_ : ∀ {Θ Θ′ Δ}
    → TyEnv Θ Δ → ℕ → TyEnv Θ′ Δ → Set where
  ≼-refl : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      ----------------
    → Ψ ≼[ zero ] Ψ

  ≼-ν : ∀ {Θ Θ′ Δ k} {Ψ : TyEnv Θ Δ}
      {Ψ′ : TyEnv Θ′ Δ} {B : Ty Δ}
    → Ψ ≼[ k ] Ψ′
      ----------------------
    → Ψ ≼[ suc k ] (Ψ′ ,:= B)

  ≼-begin-end : ∀ {Θ Θ′ Θ″ Δ k k′}
      {Ψ : TyEnv Θ Δ} {Ψ′ : TyEnv Θ′ Δ}
      {Ψ″ : TyEnv Θ″ (suc Δ)}
      {Z : TyVar (suc Δ)} {β : TyVar Θ′}
    → Ψ ≼[ k ] Ψ′
    → (Ψ′ ,begin[ Z ≔ β ]) ≼[ k′ ] Ψ″
      ---------------------------------------
    → Ψ ≼[ k + k′ ] (Ψ″ ,end[ Z ])

  ≼-end-begin : ∀ {Θ Θ′ Θ″ Δ k k′}
      {Ψ : TyEnv Θ (suc Δ)} {Ψ′ : TyEnv Θ′ (suc Δ)}
      {Ψ″ : TyEnv Θ″ Δ} {X : TyVar (suc Δ)}
      {α : TyVar Θ} {β : TyVar Θ″}
    → Ψ ∋typ X ≔ α
    → Ψ ≼[ k ] Ψ′
    → (Ψ′ ,end[ X ]) ≼[ k′ ] Ψ″
    → Shifted (k + k′) α β
      ------------------------------------------
    → Ψ ≼[ k + k′ ] (Ψ″ ,begin[ X ≔ β ])

shiftAlong : ∀ {Θ Θ′ Δ k} {Ψ : TyEnv Θ Δ} {Ψ′ : TyEnv Θ′ Δ}
  → Ψ ≼[ k ] Ψ′ → TyVar Θ → TyVar Θ′
shiftAlong ≼-refl α = α
shiftAlong (≼-ν extension) α = suc (shiftAlong extension α)
shiftAlong (≼-begin-end extension region) α =
  shiftAlong region (shiftAlong extension α)
shiftAlong (≼-end-begin slot∈ extension region shifted) α =
  shiftAlong region (shiftAlong extension α)

data _∋rep_≔_ : TyEnv Θ Δ → TyVar Θ → Ty Δ → Set where
  found : ∀ {Θ Θ′ Δ k} {Ψ : TyEnv Θ Δ} {A : Ty Δ}
      {Ψ′ : TyEnv Θ′ Δ}
    → (extension : (Ψ ,:= A) ≼[ k ] Ψ′)
      ---------------------------------------
    → Ψ′ ∋rep shiftAlong extension zero ≔ A

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

private
  variable
    F M N : Term Θ Δ

infix 4 _∣_⊢_⦂_

data _∣_⊢_⦂_ : TyEnv Θ Δ → TermCtx Δ → Term Θ Δ → Ty Δ
  → Set where
  ⊢` :
      Γ ∋ x ⦂ A
      -------------------
    → Ψ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ :
      Ψ ∣ A ∷ Γ ⊢ M ⦂ B
      -----------------------------
    → Ψ ∣ Γ ⊢ (ƛ A ˙ M) ⦂ (A ⇒ B)

  ⊢· :
      Ψ ∣ Γ ⊢ F ⦂ (A ⇒ B)
    → Ψ ∣ Γ ⊢ M ⦂ A
      ---------------------
    → Ψ ∣ Γ ⊢ (F · M) ⦂ B

  -- DEFERRED: value restriction
  ⊢Λ :
      Ψ ,typ ∣ renameCtx suc Γ ⊢ M ⦂ A
      ----------------------------------
    → Ψ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢⦂∀ :
      Ψ ∣ Γ ⊢ F ⦂ `∀ C
      ----------------------------------
    → Ψ ∣ Γ ⊢ F ⦂∀ C [ A ] ⦂ C [ A ]ᵗ

  ⊢$ : ∀ (κ : Const)
      ---------------------------
    → Ψ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ :
      (op : Prim)
    → Ψ ∣ Γ ⊢ F ⦂ primArgTy op
    → Ψ ∣ Γ ⊢ M ⦂ primArgTy op
      -------------------------------------------
    → Ψ ∣ Γ ⊢ (F ⊕[ op ] M) ⦂ primResultTy op

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
    → Ψ ∋rep α ≔ C
    → ⊢↑[ Y ⦂ wkᵗ Y C ] c ⦂ A ↝ wkᵗ Y B
    → Ψ ,begin[ Y ≔ α ] ∣ [] ⊢ M ⦂ A
      --------------------------------
    → Ψ ∣ Γ ⊢ M ↑[ Y ≔ α ] c ⦂ B

  -- Reveal begins the lifetime of its abstract slot.  Conceal checks its
  -- closed interior after appending the matching popping marker; the
  -- conclusion keeps the unmodified telescope in which that slot is live.
  ⊢conceal : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
      {Γ′ : TermCtx (suc Δ)}
      {M : Term Θ Δ}
      {A C : Ty Δ} {B : Ty (suc Δ)} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
    → Ψ ∋typ Y ≔ α
    → (Ψ ,end[ Y ]) ∋rep α ≔ C
    → ⊢↓[ Y ⦂ wkᵗ Y C ] c ⦂ wkᵗ Y A ↝ B
    → Ψ ,end[ Y ] ∣ [] ⊢ M ⦂ A
      ------------------------------------------
    → Ψ ∣ Γ′ ⊢ M ↓[ Y ≔ α ] c ⦂ B

  ⊢blame :
      ---------------------
      Ψ ∣ Γ ⊢ blame ⦂ A
