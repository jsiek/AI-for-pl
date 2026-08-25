module alt.ThetaTyping where

-- File Charter:
--   * Defines typing for the Θ-indexed alternative syntax.  The binder
--     telescope `TyEnv` holds type-variable entries (with their recorded
--     insertion position) and anchor:=representation entries; term
--     variables live in a separate `TermCtx` list, so a context with no
--     term variables is the literal `[]` — closed interiors for ν and
--     the crossings are structural, with no erasure.
--   * Crossing-slot entries record both their insertion position and anchor.
--     Lexical Λ entries are separate: a lexical variable is always newest in
--     its prefix, and later prefix insertions are strictly older, so its
--     formerly constant position argument carried no information.
--   * Representations are written in the regular scope at their entry; anchor
--     lookup transports them lazily across begin/end markers.  Telescope
--     entries are never rewritten when a scope ends.  Anchors never occur in
--     regular types `Ty Δ`.
--   * Term variables cross only Λ's type-variable entry, by weakening the
--     term list wholesale (renameCtx), as in the live calculus.

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Nat using (ℕ; zero; suc)
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
  _,:=_ : TyEnv Θ Δ → Ty Δ → TyEnv (suc Θ) Δ  -- anchor bound by a ν
  _,end[_] : TyEnv Θ (suc Δ) → TyVar (suc Δ) → TyEnv Θ Δ

private
  variable
    Ψ Ψ′ : TyEnv Θ Δ
    Γ Γ′ : TermCtx Δ
    A B C : Ty Δ
    x y z : Var
    a b : TyVar Θ

data Mode : (scope : TyCtx) → Set where
  know : ∀ {Δ} → List (TyVar Δ) → Mode Δ
  opaq : ∀ {Δ} → Mode Δ

dropSlot : ∀ {Δ}
  → TyVar (suc Δ) → List (TyVar (suc Δ)) → List (TyVar Δ)
dropSlot W [] = []
dropSlot W (X ∷ pending) with W ≟ X
dropSlot W (.W ∷ pending) | yes refl = dropSlot W pending
dropSlot W (X ∷ pending) | no W≠X =
  punchOut W X W≠X ∷ dropSlot W pending

infix 4 _∋typ_≔_

-- Slot lookup: `Ψ ∋typ Y ≔ α` finds the begin entry that binds the
-- type variable Y in Ψ and returns its recorded anchor α.
data _∋typ_≔_ : ∀ {Θ Δ}
    → TyEnv Θ Δ → TyVar Δ → TyVar Θ
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

infix 4 _∋rep[_]_≔_

data _∋rep[_]_≔_ : ∀ {Θ Δ}
    → TyEnv Θ Δ → Mode Δ → TyVar Θ → Ty Δ → Set where
  Z : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {A : Ty Δ} {mode}
      ---------------------
    → Ψ ,:= A ∋rep[ mode ] zero ≔ A

  S : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {a : TyVar Θ}
      {A B : Ty Δ} {mode}
    → Ψ ∋rep[ mode ] a ≔ A
      ----------------------
    → Ψ ,:= B ∋rep[ mode ] suc a ≔ A

  skip-begin-pending : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a β : TyVar Θ} {A : Ty Δ}
      {Y : TyVar (suc Δ)} {pending}
    → Y ∈ pending
    → Ψ ∋rep[ know (dropSlot Y pending) ] a ≔ A
      ---------------------------------
    → Ψ ,begin[ Y ≔ β ] ∋rep[ know pending ] a ≔ wkᵗ Y A

  skip-begin-live : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a β : TyVar Θ} {A : Ty Δ}
      {Y : TyVar (suc Δ)} {pending}
    → Y ∉ pending
    → Ψ ∋rep[ opaq ] a ≔ A
      ---------------------------------
    → Ψ ,begin[ Y ≔ β ] ∋rep[ know pending ] a ≔ wkᵗ Y A

  skip-begin-opaq : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a β : TyVar Θ} {A : Ty Δ}
      {Y : TyVar (suc Δ)}
    → Ψ ∋rep[ opaq ] a ≔ A
      ---------------------------------
    → Ψ ,begin[ Y ≔ β ] ∋rep[ opaq ] a ≔ wkᵗ Y A

  skip-lexical-know : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a : TyVar Θ} {A : Ty Δ} {pending pending′}
    → map suc pending ≡ pending′
    → Ψ ∋rep[ know pending ] a ≔ A
      ------------------------
    → Ψ ,typ ∋rep[ know pending′ ] a ≔ ⇑ᵗ A

  skip-lexical-opaq : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a : TyVar Θ} {A : Ty Δ}
    → Ψ ∋rep[ opaq ] a ≔ A
      ------------------------
    → Ψ ,typ ∋rep[ opaq ] a ≔ ⇑ᵗ A

  skip-end : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
      {Y : TyVar (suc Δ)} {α a : TyVar Θ}
      {A : Ty (suc Δ)} {B C : Ty Δ} {pending}
    → Ψ ∋typ Y ≔ α
    → Ψ ∋rep[ know (Y ∷ map (punchIn Y) pending) ] α ≔ wkᵗ Y C
    → Ψ ∋rep[ know (Y ∷ map (punchIn Y) pending) ] a ≔ A
    → substᵗ (resolveSubᵗ Y C) A ≡ B
      --------------------------------------------
    → Ψ ,end[ Y ] ∋rep[ know pending ] a ≔ B

-- "reveal is opaque on the inside and knowledge on the outside, conceal is
-- the dual."  A representation lookup begins at `know []`.  An end pushes
-- its slot onto the pending list and resolves that slot in the result only.
-- Its matching begin removes the pending slot; a live begin instead changes
-- the route to `opaq`.  Opaque lookup has no end-marker constructor, so an
-- end is refused rather than silently crossed.
-- In particular, ending a scope appends syntax to the telescope: no stored
-- entry is substituted, punched out, or otherwise rewritten.

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
      Ψ ,typ ∣ renameCtx suc Γ ⊢ M ⦂ A
      ----------------------------------
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
    → Ψ ∋rep[ know [] ] α ≔ C
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
    → (Ψ ,end[ Y ]) ∋rep[ know [] ] α ≔ C
    → ⊢↓[ Y ⦂ wkᵗ Y C ] c ⦂ wkᵗ Y A ↝ B
    → Ψ ,end[ Y ] ∣ [] ⊢ M ⦂ A
      ------------------------------------------
    → Ψ ∣ Γ′ ⊢ M ↓[ Y ≔ α ] c ⦂ B

  ⊢blame :
      ---------------------
      Ψ ∣ Γ ⊢ blame ⦂ A
