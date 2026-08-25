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
--     lookup transports an internal `Ty⁺` payload across begin/end markers.
--     An end is the sole introduction site for `ref`; a matching later begin
--     re-aliases that reference to its abstract slot, while a query discharges
--     references whose scopes remain dead.  Telescope entries are never
--     rewritten when a scope ends.  Anchors never occur in regular `Ty Δ`.
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
-- Lookup-internal representation types
------------------------------------------------------------------------

infixr 7 _⇒⁺_
infix 6 `∀⁺

data Ty⁺ (Θ : AnchorCtx) : TyCtx → Set where
  ＇⁺_ : ∀ {Δ} → TyVar Δ → Ty⁺ Θ Δ
  ‵⁺_ : ∀ {Δ} → Base → Ty⁺ Θ Δ
  ★⁺ : ∀ {Δ} → Ty⁺ Θ Δ
  _⇒⁺_ : ∀ {Δ} → Ty⁺ Θ Δ → Ty⁺ Θ Δ → Ty⁺ Θ Δ
  `∀⁺ : ∀ {Δ} → Ty⁺ Θ (suc Δ) → Ty⁺ Θ Δ
  ref : ∀ {Δ} → TyVar Θ → Ty⁺ Θ Δ

⌜_⌝ : ∀ {Θ Δ} → Ty Δ → Ty⁺ Θ Δ
⌜ ＇ X ⌝ = ＇⁺ X
⌜ ‵ ι ⌝ = ‵⁺ ι
⌜ ★ ⌝ = ★⁺
⌜ A ⇒ B ⌝ = ⌜ A ⌝ ⇒⁺ ⌜ B ⌝
⌜ `∀ A ⌝ = `∀⁺ ⌜ A ⌝

renameᵗ⁺ : ∀ {Θ Δ Δ′} → (TyVar Δ → TyVar Δ′)
  → Ty⁺ Θ Δ → Ty⁺ Θ Δ′
renameᵗ⁺ ρ (＇⁺ X) = ＇⁺ (ρ X)
renameᵗ⁺ ρ (‵⁺ ι) = ‵⁺ ι
renameᵗ⁺ ρ ★⁺ = ★⁺
renameᵗ⁺ ρ (A⁺ ⇒⁺ B⁺) = renameᵗ⁺ ρ A⁺ ⇒⁺ renameᵗ⁺ ρ B⁺
renameᵗ⁺ ρ (`∀⁺ A⁺) = `∀⁺ (renameᵗ⁺ (extᵗ ρ) A⁺)
renameᵗ⁺ ρ (ref α) = ref α

renameᶠ⁺ : ∀ {Θ Θ′ Δ} → (TyVar Θ → TyVar Θ′)
  → Ty⁺ Θ Δ → Ty⁺ Θ′ Δ
renameᶠ⁺ ρ (＇⁺ X) = ＇⁺ X
renameᶠ⁺ ρ (‵⁺ ι) = ‵⁺ ι
renameᶠ⁺ ρ ★⁺ = ★⁺
renameᶠ⁺ ρ (A⁺ ⇒⁺ B⁺) = renameᶠ⁺ ρ A⁺ ⇒⁺ renameᶠ⁺ ρ B⁺
renameᶠ⁺ ρ (`∀⁺ A⁺) = `∀⁺ (renameᶠ⁺ ρ A⁺)
renameᶠ⁺ ρ (ref α) = ref (ρ α)

end⁺ : ∀ {Θ Δ} → TyVar (suc Δ) → TyVar Θ
  → Ty⁺ Θ (suc Δ) → Ty⁺ Θ Δ
end⁺ Y β (＇⁺ X) with Y ≟ X
end⁺ Y β (＇⁺ .Y) | yes refl = ref β
end⁺ Y β (＇⁺ X) | no Y≢X = ＇⁺ (punchOut Y X Y≢X)
end⁺ Y β (‵⁺ ι) = ‵⁺ ι
end⁺ Y β ★⁺ = ★⁺
end⁺ Y β (A⁺ ⇒⁺ B⁺) = end⁺ Y β A⁺ ⇒⁺ end⁺ Y β B⁺
end⁺ Y β (`∀⁺ A⁺) = `∀⁺ (end⁺ (suc Y) β A⁺)
end⁺ Y β (ref α) = ref α

begin⁺ : ∀ {Θ Δ} → TyVar (suc Δ) → TyVar Θ
  → Ty⁺ Θ Δ → Ty⁺ Θ (suc Δ)
begin⁺ Y β (＇⁺ X) = ＇⁺ (punchIn Y X)
begin⁺ Y β (‵⁺ ι) = ‵⁺ ι
begin⁺ Y β ★⁺ = ★⁺
begin⁺ Y β (A⁺ ⇒⁺ B⁺) = begin⁺ Y β A⁺ ⇒⁺ begin⁺ Y β B⁺
begin⁺ Y β (`∀⁺ A⁺) = `∀⁺ (begin⁺ (suc Y) β A⁺)
begin⁺ Y β (ref α) with β ≟ α
begin⁺ Y β (ref .β) | yes refl = ＇⁺ Y
begin⁺ Y β (ref α) | no β≢α = ref α

typ⁺ : ∀ {Θ Δ} → Ty⁺ Θ Δ → Ty⁺ Θ (suc Δ)
typ⁺ = renameᵗ⁺ suc

wkᶠ⁺ : ∀ {Θ Δ} → Ty⁺ Θ Δ → Ty⁺ (suc Θ) Δ
wkᶠ⁺ = renameᶠ⁺ suc

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

infix 4 _∋rep⁺_≔_ _⊢_⇓_ _∋rep_≔_

-- Raw lookup transports `Ty⁺` structurally.  `end⁺` is the single
-- introduction site for an anchor reference; `begin⁺` re-aliases every
-- matching reference, adjacent or not, to the new abstract slot.
data _∋rep⁺_≔_ : ∀ {Θ Δ}
    → TyEnv Θ Δ → TyVar Θ → Ty⁺ Θ Δ → Set where
  Z : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {A : Ty Δ}
      --------------------------------
    → Ψ ,:= A ∋rep⁺ zero ≔ wkᶠ⁺ ⌜ A ⌝

  S : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {a : TyVar Θ}
      {A⁺ : Ty⁺ Θ Δ} {B : Ty Δ}
    → Ψ ∋rep⁺ a ≔ A⁺
      ----------------------------------
    → Ψ ,:= B ∋rep⁺ suc a ≔ wkᶠ⁺ A⁺

  skip-begin : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a β : TyVar Θ} {A⁺ : Ty⁺ Θ Δ}
      {Y : TyVar (suc Δ)}
    → Ψ ∋rep⁺ a ≔ A⁺
      -------------------------------------------------
    → Ψ ,begin[ Y ≔ β ] ∋rep⁺ a ≔ begin⁺ Y β A⁺

  skip-typ : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
      {a : TyVar Θ} {A⁺ : Ty⁺ Θ Δ}
    → Ψ ∋rep⁺ a ≔ A⁺
      -----------------------------
    → Ψ ,typ ∋rep⁺ a ≔ typ⁺ A⁺

  skip-end : ∀ {Θ Δ} {Ψ : TyEnv Θ (suc Δ)}
      {Y : TyVar (suc Δ)} {β a : TyVar Θ}
      {A⁺ : Ty⁺ Θ (suc Δ)}
    → Ψ ∋typ Y ≔ β
    → Ψ ∋rep⁺ a ≔ A⁺
      -----------------------------------------------
    → Ψ ,end[ Y ] ∋rep⁺ a ≔ end⁺ Y β A⁺

-- Query discharge is deliberately mutual with the public lookup.  A ref
-- follows its anchor only when the query is finally discharged; under `∀⁺`
-- the query enters the lexical telescope, so the representation is weakened
-- at the binder in the same way as every ordinary type payload.
mutual
  data _⊢_⇓_ : ∀ {Θ Δ}
      → TyEnv Θ Δ → Ty⁺ Θ Δ → Ty Δ → Set where
    ⇓-var : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {X : TyVar Δ}
        ------------------
      → Ψ ⊢ ＇⁺ X ⇓ ＇ X

    ⇓-base : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {ι : Base}
        ------------------
      → Ψ ⊢ ‵⁺ ι ⇓ ‵ ι

    ⇓-star : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
        ---------------
      → Ψ ⊢ ★⁺ ⇓ ★

    ⇓-fun : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
        {A⁺ B⁺ : Ty⁺ Θ Δ} {A B : Ty Δ}
      → Ψ ⊢ A⁺ ⇓ A
      → Ψ ⊢ B⁺ ⇓ B
        -----------------------
      → Ψ ⊢ A⁺ ⇒⁺ B⁺ ⇓ A ⇒ B

    ⇓-all : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
        {A⁺ : Ty⁺ Θ (suc Δ)} {A : Ty (suc Δ)}
      → Ψ ,typ ⊢ A⁺ ⇓ A
        -------------------
      → Ψ ⊢ `∀⁺ A⁺ ⇓ `∀ A

    ⇓-ref : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
        {β : TyVar Θ} {C : Ty Δ}
      → Ψ ∋rep β ≔ C
        -------------
      → Ψ ⊢ ref β ⇓ C

  data _∋rep_≔_ : ∀ {Θ Δ}
      → TyEnv Θ Δ → TyVar Θ → Ty Δ → Set where
    ∋rep-of : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
        {a : TyVar Θ} {A⁺ : Ty⁺ Θ Δ} {A : Ty Δ}
      → Ψ ∋rep⁺ a ≔ A⁺
      → Ψ ⊢ A⁺ ⇓ A
        ---------------
      → Ψ ∋rep a ≔ A

-- No crossing is refused.  Ends defer abstract occurrences as refs; begins
-- re-alias matching refs, and only a public lookup query resolves references
-- whose anchors remain dead.

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
