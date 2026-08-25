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

infixl 5 _,typ[_≔_] _,typ _,end[_]
infixl 5 _,:=_

data TyEnv : AnchorCtx → TyCtx → Set where
  ∅ : TyEnv zero zero
  _,typ[_≔_] : TyEnv Θ Δ → TyVar (suc Δ) → TyVar Θ
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

data SlotMode : Set where
  slot-know slot-opaq : SlotMode

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

infix 4 _∋typ[_]_≔_

data _∋typ[_]_≔_ : ∀ {Θ Δ}
    → TyEnv Θ Δ → SlotMode → TyVar Δ → TyVar Θ
    → Set where
  here-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {mode}
      {Y : TyVar (suc Δ)} {α : TyVar Θ}
      ---------------------------------
    → (Ψ ,typ[ Y ≔ α ]) ∋typ[ mode ] Y ≔ α

  skip-cross-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {Y : TyVar Δ} {α : TyVar Θ}
      {Z : TyVar (suc Δ)} {β : TyVar Θ} {mode}
    → Ψ ∋typ[ mode ] Y ≔ α
      -----------------------------------------------------
    → (Ψ ,typ[ Z ≔ β ]) ∋typ[ mode ] punchIn Z Y ≔ α

  skip-lexical-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {Y : TyVar Δ} {α : TyVar Θ} {mode}
    → Ψ ∋typ[ mode ] Y ≔ α
      -----------------------------
    → (Ψ ,typ) ∋typ[ mode ] (suc Y) ≔ α

  skip-visible-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {Y : TyVar Δ} {α : TyVar Θ} {A : Ty Δ} {mode}
    → Ψ ∋typ[ mode ] Y ≔ α
      --------------------------------
    → (Ψ ,:= A) ∋typ[ mode ] Y ≔ suc α

  skip-end-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
      {Y : TyVar (suc Δ)} {X : TyVar Δ} {α : TyVar Θ} {mode}
    → Ψ ∋typ[ mode ] punchIn Y X ≔ α
      -------------------------------------------------
    → (Ψ ,end[ Y ]) ∋typ[ mode ] X ≔ α

infix 4 _∋rep[_]_≔_

data _∋rep[_]_≔_ : ∀ {Θ Δ}
    → TyEnv Θ Δ → Mode Δ → TyVar Θ → Ty Δ → Set where
  Z : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {A : Ty Δ} {mode}
      ---------------------
    → _∋rep[_]_≔_ (Ψ ,:= A) mode zero A

  S : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {a : TyVar Θ}
      {A B : Ty Δ} {mode}
    → _∋rep[_]_≔_ Ψ mode a A
      ----------------------
    → _∋rep[_]_≔_ (Ψ ,:= B) mode (suc a) A

  skip-typ-pending : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a β : TyVar Θ} {A : Ty Δ}
      {Y : TyVar (suc Δ)} {pending}
    → Y ∈ pending
    → _∋rep[_]_≔_ Ψ (know (dropSlot Y pending)) a A
      ---------------------------------
    → _∋rep[_]_≔_ (Ψ ,typ[ Y ≔ β ]) (know pending) a (wkᵗ Y A)

  skip-typ-live : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a β : TyVar Θ} {A : Ty Δ}
      {Y : TyVar (suc Δ)} {pending}
    → Y ∉ pending
    → _∋rep[_]_≔_ Ψ opaq a A
      ---------------------------------
    → _∋rep[_]_≔_ (Ψ ,typ[ Y ≔ β ]) (know pending) a (wkᵗ Y A)

  skip-typ-opaq : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a β : TyVar Θ} {A : Ty Δ}
      {Y : TyVar (suc Δ)}
    → _∋rep[_]_≔_ Ψ opaq a A
      ---------------------------------
    → _∋rep[_]_≔_ (Ψ ,typ[ Y ≔ β ]) opaq a (wkᵗ Y A)

  skip-lexical-know : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a : TyVar Θ} {A : Ty Δ} {pending pending′}
    → map suc pending ≡ pending′
    → _∋rep[_]_≔_ Ψ (know pending) a A
      ------------------------
    → _∋rep[_]_≔_ (Ψ ,typ) (know pending′) a (⇑ᵗ A)

  skip-lexical-opaq : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a : TyVar Θ} {A : Ty Δ}
    → _∋rep[_]_≔_ Ψ opaq a A
      ------------------------
    → _∋rep[_]_≔_ (Ψ ,typ) opaq a (⇑ᵗ A)

  skip-end : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
      {Y : TyVar (suc Δ)} {α a : TyVar Θ}
      {A : Ty (suc Δ)} {B C : Ty Δ} {pending}
    → Ψ ∋typ[ slot-know ] Y ≔ α
    → _∋rep[_]_≔_ Ψ
        (know (Y ∷ map (punchIn Y) pending)) α (wkᵗ Y C)
    → _∋rep[_]_≔_ Ψ
        (know (Y ∷ map (punchIn Y) pending)) a A
    → substᵗ (resolveSubᵗ Y C) A ≡ B
      --------------------------------------------
    → _∋rep[_]_≔_ (Ψ ,end[ Y ]) (know pending) a B

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
    → Ψ ,typ[ Y ≔ α ] ∣ [] ⊢ M ⦂ A
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
    → Ψ ∋typ[ slot-know ] Y ≔ α
    → (Ψ ,end[ Y ]) ∋rep[ know [] ] α ≔ C
    → ⊢↓[ Y ⦂ wkᵗ Y C ] c ⦂ wkᵗ Y A ↝ B
    → Ψ ,end[ Y ] ∣ [] ⊢ M ⦂ A
      ------------------------------------------
    → Ψ ∣ Γ′ ⊢ M ↓[ Y ≔ α ] c ⦂ B

  ⊢blame :
      ---------------------
      Ψ ∣ Γ ⊢ blame ⦂ A
