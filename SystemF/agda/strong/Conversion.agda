module strong.Conversion where

-- Strong System F v8 — conversions: lists of conversion elements.
--
-- The four atomic elements each cross the introduction of one name
-- assignment, and each carries its ADDRESS:
--
--   seal X α     seal{-X:=α}    : A ⇝ X   renames via α's representation
--   unseal X α   unseal{+X:=α}  : X ⇝ A
--   hide X α     id{-X:=α}      : A ⇝ A    identity conceal crossing
--   show X α     id{+X:=α}      : A ⇝ A    identity reveal crossing
--
-- Each carries BOTH the name and the address, exactly as the notes
-- write it.  The address is what `fuse` cancels on; the NAME is what
-- makes the crossing's context movement a function of the syntax — the
-- pop judgment skips binder assignments, so an element under a
-- ∀-component may cross an assignment lying below those binders, and
-- only the name says how deep.
--
-- The structural elements delegate their crossing to their components.
-- The terminator `id A` is STRICTLY REFLEXIVE — all context movement is
-- in the elements — so the v7 tail judgment is gone: one typing
-- judgment suffices.  The stack discipline is typing: an atomic
-- element's premise `Γ ▷ X := α ⇒ Γ′` pops only the newest crossing
-- assignment.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (_≟_; _<?_)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; substᵗ; extᵗ;
         shiftAtᵗ)
open import strong.RepresentationTypes
open import strong.Ctx

------------------------------------------------------------------------
-- Syntax
------------------------------------------------------------------------

mutual
  data ConvElt : Set where
    seal   : ℕ → Addr → ConvElt
    unseal : ℕ → Addr → ConvElt
    hide   : ℕ → Addr → ConvElt
    show   : ℕ → Addr → ConvElt
    _↦_    : Conv → Conv → ConvElt
    all    : Conv → ConvElt

  data Conv : Set where
    id   : Ty → Conv
    _∷ᶜ_ : ConvElt → Conv → Conv

infixr 7 _↦_
infixr 6 _∷ᶜ_

mutual
  -- Renaming a conversion's NAMES.  There is no address renaming to
  -- pair it with any more: a `∀` binds a type variable, so descending
  -- under an `all` moves no address.
  renElt : Renameᵗ → ConvElt → ConvElt
  renElt ρ (seal X α)   = seal (ρ X) α
  renElt ρ (unseal X α) = unseal (ρ X) α
  renElt ρ (hide X α)   = hide (ρ X) α
  renElt ρ (show X α)   = show (ρ X) α
  renElt ρ (s ↦ t)    = renConv ρ s ↦ renConv ρ t
  renElt ρ (all s)    = all (renConv (extᵗ ρ) s)

  renConv : Renameᵗ → Conv → Conv
  renConv ρ (id A)    = id (renameᵗ ρ A)
  renConv ρ (ĉ ∷ᶜ c) = renElt ρ ĉ ∷ᶜ renConv ρ c

-- The BASE renaming of a conversion.  An `all` binds a STACK address,
-- so the renaming passes through it unextended — and names are
-- untouched, since a base push adds none.
mutual
  renEltᵉ : Renameᵇ → ConvElt → ConvElt
  renEltᵉ σ (seal X α)   = seal X (renᵃᵉ σ α)
  renEltᵉ σ (unseal X α) = unseal X (renᵃᵉ σ α)
  renEltᵉ σ (hide X α)   = hide X (renᵃᵉ σ α)
  renEltᵉ σ (show X α)   = show X (renᵃᵉ σ α)
  renEltᵉ σ (s ↦ t)     = renConvᵉ σ s ↦ renConvᵉ σ t
  renEltᵉ σ (all s)     = all (renConvᵉ σ s)

  renConvᵉ : Renameᵇ → Conv → Conv
  renConvᵉ σ (id A)    = id A
  renConvᵉ σ (ĉ ∷ᶜ c) = renEltᵉ σ ĉ ∷ᶜ renConvᵉ σ c

elts : Conv → List ConvElt
elts (id A)   = []
elts (ĉ ∷ᶜ c) = ĉ ∷ elts c

target : Conv → Ty
target (id A)   = A
target (ĉ ∷ᶜ c) = target c

attach : List ConvElt → Ty → Conv
attach []       A = id A
attach (ĉ ∷ ĉs) A = ĉ ∷ᶜ attach ĉs A

------------------------------------------------------------------------
-- Type-variable occurrence, closing, and annotation substitution
------------------------------------------------------------------------

occursᵗ : ℕ → Ty → Bool
occursᵗ X (` Y) with X ≟ Y
occursᵗ X (` Y) | yes _ = true
occursᵗ X (` Y) | no  _ = false
occursᵗ X `ℕ      = false
occursᵗ X `𝔹      = false
occursᵗ X (A ⇒ B) = occursᵗ X A ∨ occursᵗ X B
occursᵗ X (`∀ A)  = occursᵗ (suc X) A

closeEnv : ℕ → Ty → ℕ → Ty
closeEnv X S Y with X ≟ Y
closeEnv X S Y | yes _ = S
closeEnv X S Y | no _ with X <? Y
closeEnv X S Y | no _ | yes _ = ` (Y ∸ 1)
closeEnv X S Y | no _ | no  _ = ` Y

closeAt : ℕ → Ty → Ty → Ty
closeAt X S A = substᵗ (closeEnv X S) A

-- `c[X:=S]`: the crossings a conversion performs are unchanged, but
-- removing the name slot X reindexes the names ABOVE it, so an
-- element's name decrements exactly when it lies above the slot.
nameSub : ℕ → ℕ → ℕ
nameSub X Y with X <? Y
nameSub X Y | yes _ = Y ∸ 1
nameSub X Y | no _ = Y

-- Substituting `S` for the name at the SLOT X, and removing the slot.
--
-- Both the slot and `S` travel along the spine: the tail of a spine
-- lives one crossing further out, where the slot sits at a different
-- index and `S` needs re-expressing.  `slotOut`/`tyOut` say where they
-- have got to, and every recursive call is given the index of the
-- frame it actually spans — which for `↦`'s CONTRAVARIANT component is
-- the stepped one, since that component runs exterior → interior.
mutual
  slotOutElt : ConvElt → ℕ → ℕ
  slotOutElt (seal Y α)   X = shiftAtᵗ Y X
  slotOutElt (unseal Y α) X = nameSub Y X
  slotOutElt (hide Y α)   X = shiftAtᵗ Y X
  slotOutElt (show Y α)   X = nameSub Y X
  -- the element spans what its COVARIANT component spans
  slotOutElt (s ↦ t)      X = slotOut t X
  -- `all` keeps a `bind` on both sides, so the slot moves under it
  slotOutElt (all s)      X = slotOut s (suc X) ∸ 1

  tyOutElt : ConvElt → Ty → Ty
  tyOutElt (seal Y α)   S = renameᵗ (shiftAtᵗ Y) S
  tyOutElt (unseal Y α) S = renameᵗ (nameSub Y) S
  tyOutElt (hide Y α)   S = renameᵗ (shiftAtᵗ Y) S
  tyOutElt (show Y α)   S = renameᵗ (nameSub Y) S
  tyOutElt (s ↦ t)      S = tyOut t S
  tyOutElt (all s)      S = renameᵗ (nameSub 0) (tyOut s (renameᵗ suc S))

  slotOut : Conv → ℕ → ℕ
  slotOut (id A)   X = X
  slotOut (ĉ ∷ᶜ c) X = slotOut c (slotOutElt ĉ X)

  tyOut : Conv → Ty → Ty
  tyOut (id A)   S = S
  tyOut (ĉ ∷ᶜ c) S = tyOut c (tyOutElt ĉ S)

  substAnnElt : ℕ → Ty → ConvElt → ConvElt
  substAnnElt X S (seal Y α)   = seal (nameSub X Y) α
  substAnnElt X S (unseal Y α) = unseal (nameSub X Y) α
  substAnnElt X S (hide Y α)   = hide (nameSub X Y) α
  substAnnElt X S (show Y α)   = show (nameSub X Y) α
  -- `t` spans the element's own interior → exterior; `s` spans it
  -- BACKWARD, so its interior is where the slot has already moved
  substAnnElt X S (s ↦ t) =
    substAnn (slotOut t X) (tyOut t S) s ↦ substAnn X S t
  substAnnElt X S (all s) = all (substAnn (suc X) (renameᵗ suc S) s)

  substAnn : ℕ → Ty → Conv → Conv
  substAnn X S (id A)    = id (closeAt X S A)
  substAnn X S (ĉ ∷ᶜ c) =
    substAnnElt X S ĉ ∷ᶜ substAnn (slotOutElt ĉ X) (tyOutElt ĉ S) c

------------------------------------------------------------------------
-- The builders  +X(A) and -X(A)
------------------------------------------------------------------------
-- Every equation's result crosses the assignment exactly once at the
-- top level: a miss (X does not occur) crosses with the identity
-- element, a hit with the renaming element, and a split delegates the
-- crossing to its components.  `S` is the read-back of α's
-- representation on the unassigned side.  Under a `∀` the binder
-- assignment shifts the name, the address, and S.

mutual
  revTy : ℕ → Addr → Ty → Ty → Conv
  revTy X α S (` Y) with X ≟ Y
  revTy X α S (` Y) | yes _ = unseal X α ∷ᶜ id S
  revTy X α S (` Y) | no  _ = show X α ∷ᶜ id (closeAt X S (` Y))
  revTy X α S `ℕ = show X α ∷ᶜ id `ℕ
  revTy X α S `𝔹 = show X α ∷ᶜ id `𝔹
  revTy X α S (A ⇒ B) with occursᵗ X (A ⇒ B)
  revTy X α S (A ⇒ B) | false = show X α ∷ᶜ id (closeAt X S (A ⇒ B))
  revTy X α S (A ⇒ B) | true =
    (concTy X α S A ↦ revTy X α S B) ∷ᶜ id (closeAt X S (A ⇒ B))
  revTy X α S (`∀ A) with occursᵗ (suc X) A
  revTy X α S (`∀ A) | false = show X α ∷ᶜ id (closeAt X S (`∀ A))
  revTy X α S (`∀ A) | true =
    all (revTy (suc X) α (renameᵗ suc S) A) ∷ᶜ id (closeAt X S (`∀ A))

  concTy : ℕ → Addr → Ty → Ty → Conv
  concTy X α S (` Y) with X ≟ Y
  concTy X α S (` Y) | yes _ = seal X α ∷ᶜ id (` X)
  concTy X α S (` Y) | no  _ = hide X α ∷ᶜ id (` Y)
  concTy X α S `ℕ = hide X α ∷ᶜ id `ℕ
  concTy X α S `𝔹 = hide X α ∷ᶜ id `𝔹
  concTy X α S (A ⇒ B) with occursᵗ X (A ⇒ B)
  concTy X α S (A ⇒ B) | false = hide X α ∷ᶜ id (A ⇒ B)
  concTy X α S (A ⇒ B) | true =
    (revTy X α S A ↦ concTy X α S B) ∷ᶜ id (A ⇒ B)
  concTy X α S (`∀ A) with occursᵗ (suc X) A
  concTy X α S (`∀ A) | false = hide X α ∷ᶜ id (`∀ A)
  concTy X α S (`∀ A) | true =
    all (concTy (suc X) α (renameᵗ suc S) A) ∷ᶜ id (`∀ A)

------------------------------------------------------------------------
-- Composition: append, fusion, weight
------------------------------------------------------------------------

-- Appending two conversions: the first one's terminator gives way to
-- the second.  This is the RAW composition; the normalizing one is
-- `_⨟_` in strong.ConversionReduction.
infixl 5 _⧺_
_⧺_ : Conv → Conv → Conv
id A ⧺ d      = d
(ĉ ∷ᶜ c) ⧺ d = ĉ ∷ᶜ (c ⧺ d)

-- One adjacent pair of elements fuses — or does not, and `nothing` is
-- what the normal form `NF` forbids.  Cancellation compares ADDRESSES.
-- A `↦` or `all` fusion defers its component compositions as plain
-- appends; the reduction system's congruence steps finish them.
-- Cancellation compares the NAME as well as the address.  The address
-- alone is not enough in the REMOVE-then-ADD order (`unseal ∷ seal`,
-- `show ∷ hide`): both elements then pop from different contexts, and
-- an assignment removed at one depth could be re-added at another, so
-- the pair's endpoints would not meet.  With the name checked, both
-- pushes are `pushAsgn X α` of the same context — a function — so the
-- two contexts coincide.  In the ADD-then-REMOVE order the names agree
-- automatically (`pop-unique`), so the check is free.
fuse : ConvElt → ConvElt → Maybe (List ConvElt)
fuse (seal X α) (unseal Y β) with X ≟ Y | α ≟ᵃ β
fuse (seal X α) (unseal Y β) | yes _ | yes _ = just []
fuse (seal X α) (unseal Y β) | yes _ | no  _ = nothing
fuse (seal X α) (unseal Y β) | no  _ | _ = nothing
-- PROBE 2026-09-17: does the unseal/seal direction earn its keep?
fuse (unseal X α) (seal Y β) = nothing
fuse (hide X α) (show Y β) with X ≟ Y | α ≟ᵃ β
fuse (hide X α) (show Y β) | yes _ | yes _ = just []
fuse (hide X α) (show Y β) | yes _ | no  _ = nothing
fuse (hide X α) (show Y β) | no  _ | _ = nothing
fuse (show X α) (hide Y β) with X ≟ Y | α ≟ᵃ β
fuse (show X α) (hide Y β) | yes _ | yes _ = just []
fuse (show X α) (hide Y β) | yes _ | no  _ = nothing
fuse (show X α) (hide Y β) | no  _ | _ = nothing
fuse (s₁ ↦ t₁) (s₂ ↦ t₂) = just (((s₂ ⧺ s₁) ↦ (t₁ ⧺ t₂)) ∷ [])
fuse (all s) (all t) = just (all (s ⧺ t) ∷ [])
fuse (seal X α) (seal Y β) = nothing
fuse (seal X α) (hide Y β) = nothing
fuse (seal X α) (show Y β) = nothing
fuse (seal X α) (s ↦ t) = nothing
fuse (seal X α) (all s) = nothing
fuse (unseal X α) (unseal Y β) = nothing
fuse (unseal X α) (hide Y β) = nothing
fuse (unseal X α) (show Y β) = nothing
fuse (unseal X α) (s ↦ t) = nothing
fuse (unseal X α) (all s) = nothing
fuse (hide X α) (seal Y β) = nothing
fuse (hide X α) (unseal Y β) = nothing
fuse (hide X α) (hide Y β) = nothing
fuse (hide X α) (s ↦ t) = nothing
fuse (hide X α) (all s) = nothing
fuse (show X α) (seal Y β) = nothing
fuse (show X α) (unseal Y β) = nothing
fuse (show X α) (show Y β) = nothing
fuse (show X α) (s ↦ t) = nothing
fuse (show X α) (all s) = nothing
fuse (s ↦ t) (seal Y β) = nothing
fuse (s ↦ t) (unseal Y β) = nothing
fuse (s ↦ t) (hide Y β) = nothing
fuse (s ↦ t) (show Y β) = nothing
fuse (s ↦ t) (all u) = nothing
fuse (all s) (seal Y β) = nothing
fuse (all s) (unseal Y β) = nothing
fuse (all s) (hide Y β) = nothing
fuse (all s) (show Y β) = nothing
fuse (all s) (t ↦ u) = nothing

mutual
  weightElt : ConvElt → ℕ
  weightElt (seal X α)   = 1
  weightElt (unseal X α) = 1
  weightElt (hide X α)   = 1
  weightElt (show X α)   = 1
  weightElt (s ↦ t)    = suc (weight s + weight t)
  weightElt (all s)    = suc (weight s)

  weight : Conv → ℕ
  weight (id A)    = 1
  weight (ĉ ∷ᶜ c) = suc (weightElt ĉ + weight c)

weightElts : List ConvElt → ℕ
weightElts []       = zero
weightElts (ĉ ∷ ĉs) = weightElt ĉ + weightElts ĉs

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

private
  variable
    Σ : Store
    Γ Γ₁ Γ₂ Γ₃ Γᵢ Γₑ : Ctxᵗ
    A B C D : Ty
    R : RepTy
    X : ℕ
    α : Addr
    c d s t : Conv
    ĉ : ConvElt

infix 4 _∣_⊢̂_∶_⇝_⊣_
infix 4 _∣_⊢_∶_⇝_⊣_
mutual
  data _∣_⊢̂_∶_⇝_⊣_ (Σ : Store) : Ctxᵗ → ConvElt → Ty → Ty → Ctxᵗ → Set
    where
    conv-seal : Σ ∣ Γₑ ∋r α := R → Σ ∣ Γᵢ ⊢ R ⇓ A
      → Γₑ ▷ X := α ⇒ Γᵢ
      → Σ ∣ Γᵢ ⊢̂ seal X α ∶ A ⇝ ` X ⊣ Γₑ
    -- `unseal` and `show` INTRODUCE the assignment going inward, so
    -- they carry the notes' freshness condition on the side that does
    -- not have it yet.  This is what makes name-uniqueness — and hence
    -- the single-valuedness of the read-back — propagate along a
    -- conversion (see proof.CompositionTyping).
    conv-unseal : Σ ∣ Γᵢ ∋r α := R → Σ ∣ Γₑ ⊢ R ⇓ A
      → Γᵢ ▷ X := α ⇒ Γₑ → NotAssigned Γₑ α
      → Σ ∣ Γᵢ ⊢̂ unseal X α ∶ ` X ⇝ A ⊣ Γₑ
    -- An identity crossing is "the same type" in named notation; in de
    -- Bruijn form the crossed assignment inserts a name entry at depth
    -- X, so the assigned side reads the type through `shiftAtᵗ X`.
    -- `hide` and `show` are exact duals, down to their premises: each
    -- relates the SMALLER context (the one without the assignment) to
    -- the larger, well-formedness is stated at the smaller, and the
    -- freshness condition says the address is unassigned there.  The
    -- symmetry is what lets `arr` dualize a crossing into the
    -- contravariant component (see proof.ArrTyping).
    -- Each SCOPES its address in the context without the assignment,
    -- as `conv-seal`/`conv-unseal` do with their `∋r`.  Without it a
    -- crossing may name an address nothing has bound, and then `Alloc`
    -- can discharge a fresh level onto it and turn a normal pair into
    -- a cancelling one — see notes/DECISIONS.md (2026-09-15) and
    -- `proof.PreserveAlloc.alloc-claim-refuted`.
    conv-hide : Σ ∣ Γᵢ ∋a α → Γᵢ ⊢ᵗ A
      → Γₑ ▷ X := α ⇒ Γᵢ → NotAssigned Γᵢ α
      → Σ ∣ Γᵢ ⊢̂ hide X α ∶ A ⇝ renameᵗ (shiftAtᵗ X) A ⊣ Γₑ
    conv-show : Σ ∣ Γₑ ∋a α → Γₑ ⊢ᵗ A
      → Γᵢ ▷ X := α ⇒ Γₑ → NotAssigned Γₑ α
      → Σ ∣ Γᵢ ⊢̂ show X α ∶ renameᵗ (shiftAtᵗ X) A ⇝ A ⊣ Γₑ
    conv-fun : Σ ∣ Γₑ ⊢ s ∶ C ⇝ A ⊣ Γᵢ → Σ ∣ Γᵢ ⊢ t ∶ B ⇝ D ⊣ Γₑ
      → Σ ∣ Γᵢ ⊢̂ (s ↦ t) ∶ A ⇒ B ⇝ C ⇒ D ⊣ Γₑ
    conv-all : ∀ {Ssᵢ Bsᵢ Ssₑ Bsₑ}
      → Σ ∣ (bind ∷ Ssᵢ ∥ Bsᵢ) ⊢ s ∶ A ⇝ B ⊣ (bind ∷ Ssₑ ∥ Bsₑ)
      → Σ ∣ (Ssᵢ ∥ Bsᵢ) ⊢̂ all s ∶ `∀ A ⇝ `∀ B ⊣ (Ssₑ ∥ Bsₑ)

  data _∣_⊢_∶_⇝_⊣_ (Σ : Store) : Ctxᵗ → Conv → Ty → Ty → Ctxᵗ → Set
    where
    conv-id : Γ ⊢ᵗ A → Σ ∣ Γ ⊢ id A ∶ A ⇝ A ⊣ Γ
    conv-cons : Σ ∣ Γ₁ ⊢̂ ĉ ∶ A ⇝ B ⊣ Γ₂ → Σ ∣ Γ₂ ⊢ c ∶ B ⇝ C ⊣ Γ₃
      → Σ ∣ Γ₁ ⊢ ĉ ∷ᶜ c ∶ A ⇝ C ⊣ Γ₃

------------------------------------------------------------------------
-- Normal forms
------------------------------------------------------------------------

mutual
  data NFElt : ConvElt → Set where
    nf-seal   : ∀ {X α} → NFElt (seal X α)
    nf-unseal : ∀ {X α} → NFElt (unseal X α)
    nf-hide   : ∀ {X α} → NFElt (hide X α)
    nf-show   : ∀ {X α} → NFElt (show X α)
    nf-fun    : NF s → NF t → NFElt (s ↦ t)
    nf-all    : NF s → NFElt (all s)

  data IrreducibleAfter (ĉ : ConvElt) : Conv → Set where
    irr-id   : ∀ {A} → IrreducibleAfter ĉ (id A)
    irr-cons : ∀ {ḓ c} → fuse ĉ ḓ ≡ nothing
             → IrreducibleAfter ĉ (ḓ ∷ᶜ c)

  data NF : Conv → Set where
    nf-id   : ∀ {A} → NF (id A)
    nf-cons : NFElt ĉ → NF c → IrreducibleAfter ĉ c → NF (ĉ ∷ᶜ c)

------------------------------------------------------------------------
-- The views: elementwise, since identity crossings and structural
-- elements interleave in normal forms
------------------------------------------------------------------------

arr⁻ : ConvElt → Maybe (List ConvElt)
arr⁻ (seal X α)   = nothing
arr⁻ (unseal X α) = nothing
arr⁻ (hide X α)   = just (show X α ∷ [])
arr⁻ (show X α)   = just (hide X α ∷ [])
arr⁻ (s ↦ t)      = just (elts s)
arr⁻ (all s)      = nothing

arr⁺ : ConvElt → Maybe (List ConvElt)
arr⁺ (seal X α)   = nothing
arr⁺ (unseal X α) = nothing
arr⁺ (hide X α)   = just (hide X α ∷ [])
arr⁺ (show X α)   = just (show X α ∷ [])
arr⁺ (s ↦ t)      = just (elts t)
arr⁺ (all s)      = nothing

-- A hoisted crossing moves under the ∀ element's binder, so its bound
-- address shifts; `arr` introduces no binder, so `arr⁻`/`arr⁺` do not.
all⁺ : ConvElt → Maybe (List ConvElt)
all⁺ (seal X α)   = nothing
all⁺ (unseal X α) = nothing
all⁺ (hide X α)   = just (hide (suc X) α ∷ [])
all⁺ (show X α)   = just (show (suc X) α ∷ [])
all⁺ (s ↦ t)      = nothing
all⁺ (all s)      = just (elts s)

-- Fold over the element list; the contravariant side reverses.
consArr : Maybe (List ConvElt) → Maybe (List ConvElt)
  → Maybe (List ConvElt × List ConvElt)
  → Maybe (List ConvElt × List ConvElt)
consArr (just ls) (just rs) (just (Ls , Rs)) = just (Ls ++ ls , rs ++ Rs)
consArr (just ls) (just rs) nothing = nothing
consArr (just ls) nothing q = nothing
consArr nothing r q = nothing

arrElts : List ConvElt → Maybe (List ConvElt × List ConvElt)
arrElts [] = just ([] , [])
arrElts (ĉ ∷ ĉs) = consArr (arr⁻ ĉ) (arr⁺ ĉ) (arrElts ĉs)

consAllE : Maybe (List ConvElt) → Maybe (List ConvElt)
  → Maybe (List ConvElt)
consAllE (just es) (just Es) = just (es ++ Es)
consAllE (just es) nothing = nothing
consAllE nothing Es = nothing

allElts : List ConvElt → Maybe (List ConvElt)
allElts [] = just []
allElts (ĉ ∷ ĉs) = consAllE (all⁺ ĉ) (allElts ĉs)

-- The views `arr`, `allView` and `base` are assembled from these
-- folds in `strong.ConversionReduction`: their components are APPENDS,
-- which can leave a redex at the seam, so they NORMALIZE — the same
-- discipline the builders follow.

------------------------------------------------------------------------
-- Address substitution over conversions (binder discharge at `Alloc`)
------------------------------------------------------------------------
-- `Alloc` discharges a BASE binder — the `ν`'s — into a store level, so
-- this is the base family: it replaces `bse`, and `all`, which binds on
-- the stack, does not extend it.

mutual
  substAddrElt : SubstAddr → ConvElt → ConvElt
  substAddrElt σ (seal X α)   = seal X (substAddrᵉ σ α)
  substAddrElt σ (unseal X α) = unseal X (substAddrᵉ σ α)
  substAddrElt σ (hide X α)   = hide X (substAddrᵉ σ α)
  substAddrElt σ (show X α)   = show X (substAddrᵉ σ α)
  substAddrElt σ (s ↦ t)    = substAddrConv σ s ↦ substAddrConv σ t
  substAddrElt σ (all s)    = all (substAddrConv σ s)

  substAddrConv : SubstAddr → Conv → Conv
  substAddrConv σ (id A)    = id A
  substAddrConv σ (ĉ ∷ᶜ c) = substAddrElt σ ĉ ∷ᶜ substAddrConv σ c

-- Pushing and popping the assignment NAMED X.  Both are STACK
-- operations now: the base cannot get in the way, so there is no
-- transparency question, and the two are inverses.

underJustS : (List StackEnt → List StackEnt)
  → Maybe (List StackEnt) → Maybe (List StackEnt)
underJustS f (just Ss) = just (f Ss)
underJustS f nothing   = nothing

-- Descending past a `bind` takes the address out of that binder's
-- coordinates; the binder's OWN address names no assignment.
pushAsgnS : ℕ → Addr → List StackEnt → Maybe (List StackEnt)
pushAsgnS zero α Ss = just (asgn α ∷ Ss)
pushAsgnS (suc X) α [] = nothing
pushAsgnS (suc X) α (asgn β ∷ Ss) =
  underJustS (asgn β ∷_) (pushAsgnS X α Ss)
pushAsgnS (suc X) α (bind ∷ Ss) =
  underJustS (bind ∷_) (pushAsgnS X α Ss)

popAsgnS : ℕ → Addr → List StackEnt → Maybe (List StackEnt)
popAsgnS X α [] = nothing
popAsgnS zero α (asgn β ∷ Ss) with α ≟ᵃ β
popAsgnS zero α (asgn β ∷ Ss) | yes _ = just Ss
popAsgnS zero α (asgn β ∷ Ss) | no _ = nothing
popAsgnS (suc X) α (asgn β ∷ Ss) = nothing
popAsgnS zero α (bind ∷ Ss) = nothing
popAsgnS (suc X) α (bind ∷ Ss) =
  underJustS (bind ∷_) (popAsgnS X α Ss)

underJust : (List StackEnt → List StackEnt)
  → List BaseEnt → Maybe (List StackEnt) → Maybe Ctxᵗ
underJust f Bs (just Ss) = just (f Ss ∥ Bs)
underJust f Bs nothing   = nothing

pushAsgn : ℕ → Addr → Ctxᵗ → Maybe Ctxᵗ
pushAsgn X α (Ss ∥ Bs) = underJust (λ z → z) Bs (pushAsgnS X α Ss)

popAsgn : ℕ → Addr → Ctxᵗ → Maybe Ctxᵗ
popAsgn X α (Ss ∥ Bs) = underJust (λ z → z) Bs (popAsgnS X α Ss)

------------------------------------------------------------------------
-- The interior context of a conversion: `⟨c⟩(Γ)`, walking the elements
-- from the terminator inward
------------------------------------------------------------------------

mutual
  interiorElt : ConvElt → Ctxᵗ → Maybe Ctxᵗ
  interiorElt (seal X α)   Γ = popAsgn X α Γ
  interiorElt (hide X α)   Γ = popAsgn X α Γ
  interiorElt (unseal X α) Γ = pushAsgn X α Γ
  interiorElt (show X α)   Γ = pushAsgn X α Γ
  interiorElt (s ↦ t)      Γ = interior t Γ
  interiorElt (all s) (Ss ∥ Bs) with interior s (bind ∷ Ss ∥ Bs)
  interiorElt (all s) (Ss ∥ Bs) | just (bind ∷ Ss′ ∥ Bs′) = just (Ss′ ∥ Bs′)
  interiorElt (all s) (Ss ∥ Bs) | just (asgn β ∷ Ss′ ∥ Bs′) = nothing
  interiorElt (all s) (Ss ∥ Bs) | just ([] ∥ Bs′) = nothing
  interiorElt (all s) (Ss ∥ Bs) | nothing = nothing

  interior : Conv → Ctxᵗ → Maybe Ctxᵗ
  interior (id A) Γ = just Γ
  interior (ĉ ∷ᶜ c) Γ with interior c Γ
  interior (ĉ ∷ᶜ c) Γ | just Γ′ = interiorElt ĉ Γ′
  interior (ĉ ∷ᶜ c) Γ | nothing = nothing

-- The conversion-level instantiation +X(c)/-X(c) is specified by
-- composition with the builders (+X(c) ≡ +X(src c) ⨟ c[X:=S]); it
-- needs the normalizing composition, so it lands with
-- strong.ConversionReduction.  The syntactic source reader `src` is
-- name-dependent at an unseal element in de Bruijn form, so its
-- treatment is settled there as well.
