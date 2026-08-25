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
--     An end is the sole introduction site for `ref`; every later crossing
--     merely reindexes slots and leaves refs unchanged.  At query time a live
--     anchor reads abstractly through its lowest-position alias; only a dead
--     resolves through its representation.  Telescope entries are never
--     rewritten when a scope ends.  Anchors never occur in regular `Ty Δ`.
--   * Term variables cross only Λ's type-variable entry, by weakening the
--     term list wholesale (renameCtx), as in the live calculus.

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Maybe using (Maybe; just; nothing)
  renaming (map to mapMaybe)
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

begin⁺ : ∀ {Θ Δ} → TyVar (suc Δ) → Ty⁺ Θ Δ → Ty⁺ Θ (suc Δ)
begin⁺ Y (＇⁺ X) = ＇⁺ (punchIn Y X)
begin⁺ Y (‵⁺ ι) = ‵⁺ ι
begin⁺ Y ★⁺ = ★⁺
begin⁺ Y (A⁺ ⇒⁺ B⁺) = begin⁺ Y A⁺ ⇒⁺ begin⁺ Y B⁺
begin⁺ Y (`∀⁺ A⁺) = `∀⁺ (begin⁺ (suc Y) A⁺)
begin⁺ Y (ref α) = ref α

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

dropDead : ∀ {Δ} → TyVar (suc Δ) → List (TyVar (suc Δ))
  → List (TyVar Δ)
dropDead W [] = []
dropDead W (Y ∷ Ys) with W ≟ Y
dropDead W (.W ∷ Ys) | yes refl = dropDead W Ys
dropDead W (Y ∷ Ys) | no W≢Y =
  punchOut W Y W≢Y ∷ dropDead W Ys

-- Every query-scope slot currently aliasing an anchor, innermost first.
-- An end removes its own crossing and reindexes every surviving alias.
liveSlots : ∀ {Θ Δ} → TyEnv Θ Δ → TyVar Θ → List (TyVar Δ)
liveSlots ∅ ()
liveSlots (Ψ ,begin[ Y ≔ β′ ]) β with β ≟ β′
liveSlots (Ψ ,begin[ Y ≔ β′ ]) .β′ | yes refl =
  Y ∷ map (punchIn Y) (liveSlots Ψ β′)
liveSlots (Ψ ,begin[ Y ≔ β′ ]) β | no β≢β′ =
  map (punchIn Y) (liveSlots Ψ β)
liveSlots (Ψ ,typ) β = map suc (liveSlots Ψ β)
liveSlots (Ψ ,:= A) zero = []
liveSlots (Ψ ,:= A) (suc β) = liveSlots Ψ β
liveSlots (Ψ ,end[ W ]) β = dropDead W (liveSlots Ψ β)

minTyVar : ∀ {Δ} → TyVar Δ → TyVar Δ → TyVar Δ
minTyVar zero Y = zero
minTyVar (suc X) zero = zero
minTyVar (suc X) (suc Y) = suc (minTyVar X Y)

minSlot : ∀ {Δ} → List (TyVar Δ) → Maybe (TyVar Δ)
minSlot [] = nothing
minSlot (X ∷ Xs) with minSlot Xs
minSlot (X ∷ Xs) | nothing = just X
minSlot (X ∷ Xs) | just Y = just (minTyVar X Y)

-- The anchor of a crossing slot at the query point.  Lexical variables have
-- no anchor; end markers remove their own slot before this view is queried.
slotAnchor : ∀ {Θ Δ} → TyEnv Θ Δ → TyVar Δ → Maybe (TyVar Θ)
slotAnchor ∅ ()
slotAnchor (Ψ ,begin[ Y ≔ β ]) X with Y ≟ X
slotAnchor (Ψ ,begin[ Y ≔ β ]) .Y | yes refl = just β
slotAnchor (Ψ ,begin[ Y ≔ β ]) X | no Y≢X =
  slotAnchor Ψ (punchOut Y X Y≢X)
slotAnchor (Ψ ,typ) zero = nothing
slotAnchor (Ψ ,typ) (suc X) = slotAnchor Ψ X
slotAnchor (Ψ ,:= A) X = mapMaybe suc (slotAnchor Ψ X)
slotAnchor (Ψ ,end[ Y ]) X = slotAnchor Ψ (punchIn Y X)

orSlot : ∀ {Δ} → TyVar Δ → Maybe (TyVar Δ) → TyVar Δ
orSlot Y nothing = Y
orSlot Y (just Y′) = Y′

normalAlias : ∀ {Θ Δ} → TyEnv Θ Δ → TyVar Δ
  → Maybe (TyVar Θ) → TyVar Δ
normalAlias Ψ Y nothing = Y
normalAlias Ψ Y (just β) = orSlot Y (minSlot (liveSlots Ψ β))

normalVar : ∀ {Θ Δ} → TyEnv Θ Δ → TyVar Δ → TyVar Δ
normalVar Ψ Y = normalAlias Ψ Y (slotAnchor Ψ Y)

normalTy : ∀ {Θ Δ} → TyEnv Θ Δ → Ty Δ → Ty Δ
normalTy Ψ (＇ Y) = ＇ normalVar Ψ Y
normalTy Ψ (‵ ι) = ‵ ι
normalTy Ψ ★ = ★
normalTy Ψ (A ⇒ B) = normalTy Ψ A ⇒ normalTy Ψ B
normalTy Ψ (`∀ A) = `∀ (normalTy (Ψ ,typ) A)

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
-- introduction site for an anchor reference; begin and lexical crossings
-- only reindex slots, leaving refs untouched until public query discharge.
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
    → Ψ ,begin[ Y ≔ β ] ∋rep⁺ a ≔ begin⁺ Y A⁺

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

-- Query discharge is deliberately mutual with the public lookup.  Results
-- are alias-normal: an ordinary crossing variable and a live ref both use
-- their anchor's lowest-position alias; lexical variables remain verbatim;
-- a dead ref follows its representation.  The constructors are exclusive by
-- the computed `slotAnchor`, `minSlot`, and empty shapes.  Under `∀⁺` the
-- query enters the lexical telescope, so slots and ordinary payloads weaken.
mutual
  data _⊢_⇓_ : ∀ {Θ Δ}
      → TyEnv Θ Δ → Ty⁺ Θ Δ → Ty Δ → Set where
    ⇓-var-lex : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Y : TyVar Δ}
      → slotAnchor Ψ Y ≡ nothing
        -----------------------
      → Ψ ⊢ ＇⁺ Y ⇓ ＇ Y

    ⇓-var-alias : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
        {Y Y′ : TyVar Δ} {β : TyVar Θ}
      → slotAnchor Ψ Y ≡ just β
      → minSlot (liveSlots Ψ β) ≡ just Y′
        -------------------------
      → Ψ ⊢ ＇⁺ Y ⇓ ＇ Y′

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

    ⇓-ref-live : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
        {β : TyVar Θ} {Y : TyVar Δ}
      → minSlot (liveSlots Ψ β) ≡ just Y
        ----------------------
      → Ψ ⊢ ref β ⇓ ＇ Y

    ⇓-ref-dead : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
        {β : TyVar Θ} {C : Ty Δ}
      → liveSlots Ψ β ≡ []
      → Ψ ∋rep β ≔ C
        ----------------
      → Ψ ⊢ ref β ⇓ C

  data _∋rep_≔_ : ∀ {Θ Δ}
      → TyEnv Θ Δ → TyVar Θ → Ty Δ → Set where
    ∋rep-of : ∀ {Θ Δ} {Ψ : TyEnv Θ Δ}
        {a : TyVar Θ} {A⁺ : Ty⁺ Θ Δ} {A : Ty Δ}
      → Ψ ∋rep⁺ a ≔ A⁺
      → Ψ ⊢ A⁺ ⇓ A
        ---------------
      → Ψ ∋rep a ≔ A

-- No crossing is refused.  Ends defer abstract occurrences as refs; every
-- crossing thereafter merely reindexes slots.  Only a public query decides:
-- a live ref uses its lowest-position slot, while a dead ref resolves.

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
