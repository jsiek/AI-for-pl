module alt.ThetaTyping where

-- File Charter:
--   * Defines typing for the Θ-indexed alternative syntax.  The binder
--     telescope `TyEnv` holds type-variable entries (with their recorded
--     insertion position) and anchor:=representation entries.  Its live-set
--     index makes at most one crossing per anchor intrinsic; term
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
--     merely reindexes slots and leaves refs unchanged.  At query time a ref
--     re-aliases through the unique live crossing found by the telescope walk,
--     or resolves when its live-set bit is false.  Telescope entries are never
--     rewritten when a scope ends.  Anchors never occur in regular `Ty Δ`.
--   * Term variables cross only Λ's type-variable entry, by weakening the
--     term list wholesale (renameCtx), as in the live calculus.

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Bool using (Bool; false; true)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Maybe using (Maybe; just; nothing)
  renaming (map to mapMaybe)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)
import Data.Vec.Base as Vec

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

infixl 5 _,begin[_≔_]⟨_⟩ _,typ _,end[_≔_]
infixl 5 _,:=_

setLive : ∀ {Θ} → Vec.Vec Bool Θ → TyVar Θ → Bool
  → Vec.Vec Bool Θ
setLive Vec.[] () live
setLive (old Vec.∷ L) zero live = live Vec.∷ L
setLive (old Vec.∷ L) (suc α) live = old Vec.∷ setLive L α live

data TyEnv : (Θ : AnchorCtx) → TyCtx → Vec.Vec Bool Θ → Set where
  ∅ : TyEnv zero zero Vec.[]
  _,begin[_≔_]⟨_⟩ : ∀ {L}
    → TyEnv Θ Δ L
    → TyVar (suc Δ)
    → (α : TyVar Θ)
    → Vec.lookup L α ≡ false
    → TyEnv Θ (suc Δ) (setLive L α true)
  _,typ : ∀ {L} → TyEnv Θ Δ L → TyEnv Θ (suc Δ) L
  _,:=_ : ∀ {L} → TyEnv Θ Δ L → Ty Δ
    → TyEnv (suc Θ) Δ (false Vec.∷ L)
  _,end[_≔_] : ∀ {L} → TyEnv Θ (suc Δ) L
    → TyVar (suc Δ)
    → (α : TyVar Θ)
    → TyEnv Θ Δ (setLive L α false)

-- The unique query-scope slot aliasing an anchor.  Begin construction makes
-- the matching case unique.  An end records which anchor it kills; for other
-- anchors the walk only removes and reindexes the ended slot.
liveSlot? : ∀ {Θ Δ L} → TyEnv Θ Δ L → TyVar Θ
  → Maybe (TyVar Δ)
liveSlot? ∅ ()
liveSlot? (Ψ ,begin[ Y ≔ β′ ]⟨ inactive ⟩) β with β ≟ β′
liveSlot? (Ψ ,begin[ Y ≔ β′ ]⟨ inactive ⟩) .β′
    | yes refl = just Y
liveSlot? (Ψ ,begin[ Y ≔ β′ ]⟨ inactive ⟩) β
    | no β≢β′ = mapMaybe (punchIn Y) (liveSlot? Ψ β)
liveSlot? (Ψ ,typ) β = mapMaybe suc (liveSlot? Ψ β)
liveSlot? (Ψ ,:= A) zero = nothing
liveSlot? (Ψ ,:= A) (suc β) = liveSlot? Ψ β
liveSlot? (Ψ ,end[ W ≔ β′ ]) β with β ≟ β′
liveSlot? (Ψ ,end[ W ≔ β′ ]) .β′ | yes refl = nothing
liveSlot? (Ψ ,end[ W ≔ β′ ]) β | no β≢β′
    with liveSlot? Ψ β
liveSlot? (Ψ ,end[ W ≔ β′ ]) β | no β≢β′
    | nothing = nothing
liveSlot? (Ψ ,end[ W ≔ β′ ]) β | no β≢β′
    | just Y with W ≟ Y
liveSlot? (Ψ ,end[ W ≔ β′ ]) β | no β≢β′
    | just .W | yes refl = nothing
liveSlot? (Ψ ,end[ W ≔ β′ ]) β | no β≢β′
    | just Y | no W≢Y = just (punchOut W Y W≢Y)

private
  variable
    L : Vec.Vec Bool Θ
    Ψ Ψ′ : TyEnv Θ Δ L
    Γ Γ′ : TermCtx Δ
    A B C : Ty Δ
    x y z : Var
    a b : TyVar Θ

infix 4 _∋typ_≔_

-- Slot lookup: `Ψ ∋typ Y ≔ α` finds the begin entry that binds the
-- type variable Y in Ψ and returns its recorded anchor α.
data _∋typ_≔_ : ∀ {Θ Δ L}
    → TyEnv Θ Δ L → TyVar Δ → TyVar Θ
    → Set where
  found-begin : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L}
      {Y : TyVar (suc Δ)} {α : TyVar Θ}
      {inactive : Vec.lookup L α ≡ false}
      ---------------------------------
    → (Ψ ,begin[ Y ≔ α ]⟨ inactive ⟩) ∋typ Y ≔ α

  skip-begin : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L}
      {Y : TyVar Δ} {α : TyVar Θ}
      {X : TyVar (suc Δ)} {β : TyVar Θ}
      {inactive : Vec.lookup L β ≡ false}
    → Ψ ∋typ Y ≔ α
      -----------------------------------------------------
    → (Ψ ,begin[ X ≔ β ]⟨ inactive ⟩)
        ∋typ punchIn X Y ≔ α

  skip-typ : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L}
      {Y : TyVar Δ} {α : TyVar Θ}
    → Ψ ∋typ Y ≔ α
      -----------------------------
    → (Ψ ,typ) ∋typ (suc Y) ≔ α

  skip-nu-binding : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L}
      {Y : TyVar Δ} {α : TyVar Θ} {A : Ty Δ}
    → Ψ ∋typ Y ≔ α
      --------------------------------
    → (Ψ ,:= A) ∋typ Y ≔ suc α

  skip-end : ∀ {Θ Δ L} {Ψ : TyEnv Θ (suc Δ) L}
      {Y : TyVar (suc Δ)} {X : TyVar Δ} {α β : TyVar Θ}
    → Ψ ∋typ punchIn Y X ≔ α
      -------------------------------------------------
    → (Ψ ,end[ Y ≔ β ]) ∋typ X ≔ α

infix 4 _∋rep⁺_≔_ _⊢_⇓_ _∋rep_≔_

-- Raw lookup transports `Ty⁺` structurally.  `end⁺` is the single
-- introduction site for an anchor reference; begin and lexical crossings
-- only reindex slots, leaving refs untouched until public query discharge.
data _∋rep⁺_≔_ : ∀ {Θ Δ L}
    → TyEnv Θ Δ L → TyVar Θ → Ty⁺ Θ Δ → Set where
  Z : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L} {A : Ty Δ}
      --------------------------------
    → Ψ ,:= A ∋rep⁺ zero ≔ wkᶠ⁺ ⌜ A ⌝

  S : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L} {a : TyVar Θ}
      {A⁺ : Ty⁺ Θ Δ} {B : Ty Δ}
    → Ψ ∋rep⁺ a ≔ A⁺
      ----------------------------------
    → Ψ ,:= B ∋rep⁺ suc a ≔ wkᶠ⁺ A⁺

  skip-begin : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L}
      {a β : TyVar Θ} {A⁺ : Ty⁺ Θ Δ}
      {Y : TyVar (suc Δ)}
      {inactive : Vec.lookup L β ≡ false}
    → Ψ ∋rep⁺ a ≔ A⁺
      -------------------------------------------------
    → Ψ ,begin[ Y ≔ β ]⟨ inactive ⟩ ∋rep⁺ a ≔ begin⁺ Y A⁺

  skip-typ : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L}
      {a : TyVar Θ} {A⁺ : Ty⁺ Θ Δ}
    → Ψ ∋rep⁺ a ≔ A⁺
      -----------------------------
    → Ψ ,typ ∋rep⁺ a ≔ typ⁺ A⁺

  skip-end : ∀ {Θ Δ L} {Ψ : TyEnv Θ (suc Δ) L}
      {Y : TyVar (suc Δ)} {β a : TyVar Θ}
      {A⁺ : Ty⁺ Θ (suc Δ)}
    → Ψ ∋rep⁺ a ≔ A⁺
      -----------------------------------------------
    → Ψ ,end[ Y ≔ β ] ∋rep⁺ a ≔ end⁺ Y β A⁺

-- Query discharge is deliberately mutual with the public lookup.  Ordinary
-- variables remain verbatim.  A ref re-aliases through its unique live slot;
-- when the live-set bit is false it follows its representation.  Under `∀⁺`
-- the query enters the lexical telescope, so ordinary payloads weaken.
mutual
  data _⊢_⇓_ : ∀ {Θ Δ L}
      → TyEnv Θ Δ L → Ty⁺ Θ Δ → Ty Δ → Set where
    ⇓-var : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L} {Y : TyVar Δ}
        ----------------
      → Ψ ⊢ ＇⁺ Y ⇓ ＇ Y

    ⇓-base : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L} {ι : Base}
        ------------------
      → Ψ ⊢ ‵⁺ ι ⇓ ‵ ι

    ⇓-star : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L}
        ---------------
      → Ψ ⊢ ★⁺ ⇓ ★

    ⇓-fun : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L}
        {A⁺ B⁺ : Ty⁺ Θ Δ} {A B : Ty Δ}
      → Ψ ⊢ A⁺ ⇓ A
      → Ψ ⊢ B⁺ ⇓ B
        -----------------------
      → Ψ ⊢ A⁺ ⇒⁺ B⁺ ⇓ A ⇒ B

    ⇓-all : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L}
        {A⁺ : Ty⁺ Θ (suc Δ)} {A : Ty (suc Δ)}
      → Ψ ,typ ⊢ A⁺ ⇓ A
        -------------------
      → Ψ ⊢ `∀⁺ A⁺ ⇓ `∀ A

    ⇓-ref-live : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L}
        {β : TyVar Θ} {Y : TyVar Δ}
      → liveSlot? Ψ β ≡ just Y
        ----------------------
      → Ψ ⊢ ref β ⇓ ＇ Y

    ⇓-ref-dead : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L}
        {β : TyVar Θ} {C : Ty Δ}
      → Vec.lookup L β ≡ false
      → Ψ ∋rep β ≔ C
        ----------------
      → Ψ ⊢ ref β ⇓ C

  data _∋rep_≔_ : ∀ {Θ Δ L}
      → TyEnv Θ Δ L → TyVar Θ → Ty Δ → Set where
    ∋rep-of : ∀ {Θ Δ L} {Ψ : TyEnv Θ Δ L}
        {a : TyVar Θ} {A⁺ : Ty⁺ Θ Δ} {A : Ty Δ}
      → Ψ ∋rep⁺ a ≔ A⁺
      → Ψ ⊢ A⁺ ⇓ A
        ---------------
      → Ψ ∋rep a ≔ A

-- No crossing is refused.  Ends defer abstract occurrences as refs; every
-- crossing thereafter merely reindexes slots.  Only a public query decides:
-- a ref uses its unique live slot, while a false live-set bit resolves it.

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

private
  variable
    F M N : Term Θ Δ

infix 4 _∣_⊢_⦂_

data _∣_⊢_⦂_ : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
  → TyEnv Θ Δ L → TermCtx Δ → Term Θ Δ → Ty Δ → Set where
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

  ⊢reveal : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
      {Ψ : TyEnv Θ Δ L} {Γ : TermCtx Δ}
      {M : Term Θ (suc Δ)}
      {A : Ty (suc Δ)} {B C : Ty Δ} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Reveal}
      {inactive : Vec.lookup L α ≡ false}
    → Ψ ∋rep α ≔ C
    → ⊢↑[ Y ⦂ wkᵗ Y C ] c ⦂ A ↝ wkᵗ Y B
    → Ψ ,begin[ Y ≔ α ]⟨ inactive ⟩ ∣ [] ⊢ M ⦂ A
      --------------------------------
    → Ψ ∣ Γ ⊢ M ↑[ Y ≔ α ] c ⦂ B

  -- Reveal begins the lifetime of its abstract slot.  Conceal checks its
  -- closed interior after appending the matching popping marker; the
  -- conclusion keeps the unmodified telescope in which that slot is live.
  ⊢conceal : ∀ {Θ Δ} {L : Vec.Vec Bool Θ}
      {Ψ : TyEnv Θ (suc Δ) L}
      {Γ′ : TermCtx (suc Δ)}
      {M : Term Θ Δ}
      {A C : Ty Δ} {B : Ty (suc Δ)} {Y : TyVar (suc Δ)}
      {α : TyVar Θ} {c : Conceal}
    → Ψ ∋typ Y ≔ α
    → (Ψ ,end[ Y ≔ α ]) ∋rep α ≔ C
    → ⊢↓[ Y ⦂ wkᵗ Y C ] c ⦂ wkᵗ Y A ↝ B
    → Ψ ,end[ Y ≔ α ] ∣ [] ⊢ M ⦂ A
      ------------------------------------------
    → Ψ ∣ Γ′ ⊢ M ↓[ Y ≔ α ] c ⦂ B

  ⊢blame :
      ---------------------
      Ψ ∣ Γ ⊢ blame ⦂ A
