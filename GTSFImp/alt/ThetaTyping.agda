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
--     lookup weakens them across both crossing and lexical slot entries.
--     Anchors never occur in regular types `Ty Δ`.
--   * Term variables cross only Λ's type-variable entry, by weakening the
--     term list wholesale (renameCtx), as in the live calculus.

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym)
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

infixl 5 _,typ[_≔_] _,typ
infixl 5 _,:=_

data TyEnv : AnchorCtx → TyCtx → Set where
  ∅ : TyEnv zero zero
  _,typ[_≔_] : TyEnv Θ Δ → TyVar (suc Δ) → TyVar Θ
    → TyEnv Θ (suc Δ)
  _,typ : TyEnv Θ Δ → TyEnv Θ (suc Δ)
  _,:=_ : TyEnv Θ Δ → Ty Δ → TyEnv (suc Θ) Δ  -- anchor bound by a ν

anchorRep : ∀ {Θ Δ} → TyEnv Θ Δ → TyVar Θ → Ty Δ
anchorRep ∅ ()
anchorRep (Ψ ,typ[ Y ≔ β ]) α = wkᵗ Y (anchorRep Ψ α)
anchorRep (Ψ ,typ) α = ⇑ᵗ (anchorRep Ψ α)
anchorRep (Ψ ,:= A) zero = A
anchorRep (Ψ ,:= A) (suc α) = anchorRep Ψ α

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
      {Y : TyVar (suc Δ)} {β : TyVar Θ}
    → Ψ ∋ a := A
      ---------------------------------
    → (Ψ ,typ[ Y ≔ β ]) ∋ a := wkᵗ Y A

  skip-lexical : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {a} {A : Ty Δ}
    → Ψ ∋ a := A
      ------------------------
    → (Ψ ,typ) ∋ a := ⇑ᵗ A

anchorRep∈ : ∀ {Θ Δ} (Ψ : TyEnv Θ Δ) (α : TyVar Θ)
  → Ψ ∋ α := anchorRep Ψ α
anchorRep∈ ∅ ()
anchorRep∈ (Ψ ,typ[ Y ≔ β ]) α = skip-typ (anchorRep∈ Ψ α)
anchorRep∈ (Ψ ,typ) α = skip-lexical (anchorRep∈ Ψ α)
anchorRep∈ (Ψ ,:= A) zero = Z
anchorRep∈ (Ψ ,:= A) (suc α) = S (anchorRep∈ Ψ α)

anchor-lookup-unique : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
    {α : TyVar Θ} {A B : Ty Δ}
  → Ψ ∋ α := A
  → Ψ ∋ α := B
  → A ≡ B
anchor-lookup-unique Z Z = refl
anchor-lookup-unique (S A∈) (S B∈) = anchor-lookup-unique A∈ B∈
anchor-lookup-unique (skip-typ A∈) (skip-typ B∈) =
  cong (wkᵗ _) (anchor-lookup-unique A∈ B∈)
anchor-lookup-unique (skip-lexical A∈) (skip-lexical B∈) =
  cong ⇑ᵗ (anchor-lookup-unique A∈ B∈)

infix 4 _∋typ_≔_

data _∋typ_≔_ : ∀ {Θ Δ}
    → TyEnv Θ Δ → TyVar Δ → TyVar Θ → Set where
  here-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {Y : TyVar (suc Δ)} {α : TyVar Θ}
      ---------------------------------
    → (Ψ ,typ[ Y ≔ α ]) ∋typ Y ≔ α

  skip-cross-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {Y : TyVar Δ} {α : TyVar Θ}
      {Z : TyVar (suc Δ)} {β : TyVar Θ}
    → Ψ ∋typ Y ≔ α
      -----------------------------------------------------
    → (Ψ ,typ[ Z ≔ β ]) ∋typ punchIn Z Y ≔ α

  skip-lexical-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {Y : TyVar Δ} {α : TyVar Θ}
    → Ψ ∋typ Y ≔ α
      -----------------------------
    → (Ψ ,typ) ∋typ suc Y ≔ α

  skip-visible-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {Y : TyVar Δ} {α : TyVar Θ} {A : Ty Δ}
    → Ψ ∋typ Y ≔ α
      --------------------------------
    → (Ψ ,:= A) ∋typ Y ≔ suc α

------------------------------------------------------------------------
-- Total regular-slot deletion
------------------------------------------------------------------------

record DeleteView (Θ Δ : ℕ) : Set where
  constructor delete-view
  field
    deletedEnv : TyEnv Θ Δ
    deletedRep : Ty Δ

open DeleteView

-- reveal is opaque on the inside and knowledge on the outside; conceal is the dual — the conceal's subterm is instantiator-world material, which rightfully knows the representation.
-- The worker carries that representation outward.  Retained slot entries lift
-- it; later anchors resolve the deleted slot through it.  The lexical-zero
-- branch is junk-total at `★`: `_∋typ_≔_` has deliberately no constructor
-- selecting a lexical binder, so no typed conceal can observe that branch.

deleteSlot : ∀ {Θ Δ} → TyEnv Θ (suc Δ) → TyVar (suc Δ)
  → DeleteView Θ Δ
deleteSlot (Ψ ,:= A) Y with deleteSlot Ψ Y
deleteSlot (Ψ ,:= A) Y | delete-view Φ C =
  delete-view (Φ ,:= substᵗ (resolveSubᵗ Y C) A) C
deleteSlot { Δ = zero } (Ψ ,typ[ zero ≔ α ]) zero =
  delete-view Ψ (anchorRep Ψ α)
deleteSlot { Δ = suc Δ } (Ψ ,typ[ z ≔ α ]) y with z ≟ y
deleteSlot { Δ = suc Δ } (Ψ ,typ[ .y ≔ α ]) y | yes refl =
  delete-view Ψ (anchorRep Ψ α)
deleteSlot { Δ = suc Δ } (Ψ ,typ[ z ≔ α ]) y | no z≢y
    with deleteSlot Ψ (punchOut z y z≢y)
deleteSlot { Δ = suc Δ } (Ψ ,typ[ z ≔ α ]) y | no z≢y
    | delete-view Φ C =
  delete-view
    (Φ ,typ[ punchOut y z (λ y≡z → z≢y (sym y≡z)) ≔ α ])
    (wkᵗ (punchOut y z (λ y≡z → z≢y (sym y≡z))) C)
deleteSlot (Ψ ,typ) zero = delete-view Ψ ★
deleteSlot { Δ = suc Δ } (Ψ ,typ) (suc Y) with deleteSlot Ψ Y
deleteSlot { Δ = suc Δ } (Ψ ,typ) (suc Y) | delete-view Φ C =
  delete-view (Φ ,typ) (⇑ᵗ C)

infixl 6 _∖_
_∖_ : ∀ {Θ Δ} → TyEnv Θ (suc Δ) → TyVar (suc Δ) → TyEnv Θ Δ
Ψ ∖ Y = deletedEnv (deleteSlot Ψ Y)

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
    → Ψ ∋ α := C
    → ⊢↑[ Y ⦂ wkᵗ Y C ] c ⦂ A ↝ wkᵗ Y B
    → Ψ ,typ[ Y ≔ α ] ∣ [] ⊢ M ⦂ A
      --------------------------------
    → Ψ ∣ Γ ⊢ M ↑[ Y ≔ α ] c ⦂ B

  -- Reveal and ν introduce their telescope extensions in premises, so their
  -- ambient telescope remains determined there.  Conceal binds its regular
  -- slot in the conclusion; only conceal therefore deletes from an otherwise
  -- arbitrary ambient telescope before checking its closed interior.
  ⊢conceal : ∀ {Θ Δ} {Ψ′ : TyEnv Θ (suc Δ)}
      {Γ′ : TermCtx (suc Δ)}
      {M : Term Θ Δ}
      {A C : Ty Δ} {B : Ty (suc Δ)} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
    → Ψ′ ∋typ Y ≔ α
    → (Ψ′ ∖ Y) ∋ α := C
    → ⊢↓[ Y ⦂ wkᵗ Y C ] c ⦂ wkᵗ Y A ↝ B
    → (Ψ′ ∖ Y) ∣ [] ⊢ M ⦂ A
      ------------------------------------------
    → Ψ′ ∣ Γ′ ⊢ M ↓[ Y ≔ α ] c ⦂ B

  ⊢blame :
      ---------------------
      Ψ ∣ Γ ⊢ blame ⦂ A
