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

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≢_; refl; cong; sym)
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

infixl 5 _,typ[_]
infixl 5 _,:=_
infixl 5 _,opaque

data TyEnv : AnchorCtx → TyCtx → Set where
  ∅ : TyEnv zero zero
  _,typ[_] : TyEnv Θ Δ → TyVar (suc Δ) → TyEnv Θ (suc Δ)
  _,:=_ : TyEnv Θ Δ → Ty Δ → TyEnv (suc Θ) Δ  -- anchor bound by a ν
  _,opaque : TyEnv Θ Δ → TyEnv (suc Θ) Δ
    -- The anchor exists, but its representation is not expressible here.

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

  skip-opaque :
      Ψ ∋ a := A
      ----------------------
    → (Ψ ,opaque) ∋ suc a := A

  skip-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {a} {A : Ty Δ}
      {Y : TyVar (suc Δ)}
    → Ψ ∋ a := A
      -----------------------------
    → (Ψ ,typ[ Y ]) ∋ a := wkᵗ Y A

------------------------------------------------------------------------
-- Total regular-slot deletion
------------------------------------------------------------------------

-- `punchOut Y X` removes Y from a different slot X.  Its proof argument is
-- what makes the result total even in the empty predecessor context.

punchOut : ∀ {n} (Y X : Fin (suc n)) → Y ≢ X → Fin n
punchOut zero zero Y≢X = ⊥-elim (Y≢X refl)
punchOut zero (suc X) Y≢X = X
punchOut {n = suc n} (suc Y) zero Y≢X = zero
punchOut {n = suc n} (suc Y) (suc X) Y≢X =
  suc (punchOut Y X (λ Y≡X → Y≢X (cong suc Y≡X)))

-- Strengthening is deliberately executable.  A representation mentioning Y
-- cannot be expressed after Y is deleted and therefore yields `nothing`.

strengthenᵗ? : ∀ {Δ} → TyVar (suc Δ) → Ty (suc Δ) → Maybe (Ty Δ)
strengthenᵗ? Y (＇ X) with Y ≟ X
strengthenᵗ? Y (＇ .Y) | yes refl = nothing
strengthenᵗ? Y (＇ X) | no Y≢X = just (＇ punchOut Y X Y≢X)
strengthenᵗ? Y (‵ ι) = just (‵ ι)
strengthenᵗ? Y ★ = just ★
strengthenᵗ? Y (A ⇒ B) with strengthenᵗ? Y A
strengthenᵗ? Y (A ⇒ B) | nothing = nothing
strengthenᵗ? Y (A ⇒ B) | just A′ with strengthenᵗ? Y B
strengthenᵗ? Y (A ⇒ B) | just A′ | nothing = nothing
strengthenᵗ? Y (A ⇒ B) | just A′ | just B′ = just (A′ ⇒ B′)
strengthenᵗ? Y (`∀ A) with strengthenᵗ? (suc Y) A
strengthenᵗ? Y (`∀ A) | nothing = nothing
strengthenᵗ? Y (`∀ A) | just A′ = just (`∀ A′)

infixl 6 _∖_
_∖_ : ∀ {Θ Δ} → TyEnv Θ (suc Δ) → TyVar (suc Δ) → TyEnv Θ Δ
(Ψ ,:= A) ∖ Y with strengthenᵗ? Y A
(Ψ ,:= A) ∖ Y | just C = (Ψ ∖ Y) ,:= C
(Ψ ,:= A) ∖ Y | nothing = (Ψ ∖ Y) ,opaque
(Ψ ,opaque) ∖ Y = (Ψ ∖ Y) ,opaque
_∖_ {Δ = zero} (Ψ ,typ[ zero ]) zero = Ψ
_∖_ {Δ = suc Δ} (Ψ ,typ[ z ]) y with z ≟ y
_∖_ {Δ = suc Δ} (Ψ ,typ[ .y ]) y | yes refl = Ψ
_∖_ {Δ = suc Δ} (Ψ ,typ[ z ]) y | no z≢y =
  (Ψ ∖ punchOut z y z≢y)
    ,typ[ punchOut y z (λ y≡z → z≢y (sym y≡z)) ]

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

  -- Reveal and ν introduce their telescope extensions in premises, so their
  -- ambient telescope remains determined there.  Conceal binds its regular
  -- slot in the conclusion; only conceal therefore deletes from an otherwise
  -- arbitrary ambient telescope before checking its closed interior.
  ⊢conceal : ∀ {Θ Δ} {Ψ′ : TyEnv Θ (suc Δ)}
      {Γ′ : TermCtx (suc Δ)}
      {M : Term Θ Δ}
      {A C : Ty Δ} {B : Ty (suc Δ)} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
    → (Ψ′ ∖ Y) ∋ α := C
    → ⊢↓[ Y ⦂ wkᵗ Y C ] c ⦂ wkᵗ Y A ↝ B
    → (Ψ′ ∖ Y) ∣ [] ⊢ M ⦂ A
      ------------------------------------------
    → Ψ′ ∣ Γ′ ⊢ M ↓[ Y ≔ α ] c ⦂ B

  ⊢blame :
      ---------------------
      Ψ ∣ Γ ⊢ blame ⦂ A
