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

-- `Ψ ∋rep[ pending ] α ≔ A` looks up the representation type associated
-- with the ν binding of anchor α, expressed in Ψ's scope as A.  The
-- pending list holds the ended slots whose begin the walk has not yet
-- reached: crossing an end pushes its slot and resolves that slot's
-- occurrences in the result — never in the telescope.
data _∋rep[_]_≔_ : ∀ {Θ Δ}
    → TyEnv Θ Δ → List (TyVar Δ) → TyVar Θ → Ty Δ → Set where
  Z : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {A : Ty Δ} {pending}
      ---------------------
    → Ψ ,:= A ∋rep[ pending ] zero ≔ A

  S : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {a : TyVar Θ}
      {A B : Ty Δ} {pending}
    → Ψ ∋rep[ pending ] a ≔ A
      ----------------------
    → Ψ ,:= B ∋rep[ pending ] suc a ≔ A

  skip-begin : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a β : TyVar Θ} {A : Ty Δ}
      {Y : TyVar (suc Δ)} {pending}
    → Ψ ∋rep[ dropSlot Y pending ] a ≔ A
      ---------------------------------
    → Ψ ,begin[ Y ≔ β ] ∋rep[ pending ] a ≔ wkᵗ Y A

  skip-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a : TyVar Θ} {A : Ty Δ} {pending pending′}
    → map suc pending ≡ pending′
    → Ψ ∋rep[ pending ] a ≔ A
      ------------------------
    → Ψ ,typ ∋rep[ pending′ ] a ≔ ⇑ᵗ A

  skip-end : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
      {Y : TyVar (suc Δ)} {α a : TyVar Θ}
      {A : Ty (suc Δ)} {B C : Ty Δ} {pending}
    → Ψ ∋typ Y ≔ α
    → Ψ ∋rep[ Y ∷ map (punchIn Y) pending ] α ≔ wkᵗ Y C
    → Ψ ∋rep[ Y ∷ map (punchIn Y) pending ] a ≔ A
    → substᵗ (resolveSubᵗ Y C) A ≡ B
      --------------------------------------------
    → Ψ ,end[ Y ] ∋rep[ pending ] a ≔ B

-- The lookup never blocks: ∋rep is consumed only by the reveal/conceal
-- typing rules, at their own boundary telescopes — it is never used to
-- expose a representation type inside an opaque region, so no crossing
-- needs to be refused.  Ending a scope appends syntax to the telescope:
-- no stored entry is substituted, punched out, or otherwise rewritten.

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
    → Ψ ∋rep[ [] ] α ≔ C
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
    → (Ψ ,end[ Y ]) ∋rep[ [] ] α ≔ C
    → ⊢↓[ Y ⦂ wkᵗ Y C ] c ⦂ wkᵗ Y A ↝ B
    → Ψ ,end[ Y ] ∣ [] ⊢ M ⦂ A
      ------------------------------------------
    → Ψ ∣ Γ′ ⊢ M ↓[ Y ≔ α ] c ⦂ B

  ⊢blame :
      ---------------------
      Ψ ∣ Γ ⊢ blame ⦂ A
