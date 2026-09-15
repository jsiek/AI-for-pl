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
  renElt : Renameᵗ → Renameᵇ → ConvElt → ConvElt
  renElt ρ σ (seal X α)   = seal (ρ X) (renᵃ σ α)
  renElt ρ σ (unseal X α) = unseal (ρ X) (renᵃ σ α)
  renElt ρ σ (hide X α)   = hide (ρ X) (renᵃ σ α)
  renElt ρ σ (show X α)   = show (ρ X) (renᵃ σ α)
  renElt ρ σ (s ↦ t)    = renConv ρ σ s ↦ renConv ρ σ t
  renElt ρ σ (all s)    = all (renConv (extᵗ ρ) (extᵇ σ) s)

  renConv : Renameᵗ → Renameᵇ → Conv → Conv
  renConv ρ σ (id A)    = id (renameᵗ ρ A)
  renConv ρ σ (ĉ ∷ᶜ c) = renElt ρ σ ĉ ∷ᶜ renConv ρ σ c

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

mutual
  substAnnElt : ℕ → Ty → ConvElt → ConvElt
  substAnnElt X S (seal Y α)   = seal (nameSub X Y) α
  substAnnElt X S (unseal Y α) = unseal (nameSub X Y) α
  substAnnElt X S (hide Y α)   = hide (nameSub X Y) α
  substAnnElt X S (show Y α)   = show (nameSub X Y) α
  substAnnElt X S (s ↦ t)    = substAnn X S s ↦ substAnn X S t
  substAnnElt X S (all s)    = all (substAnn (suc X) (renameᵗ suc S) s)

  substAnn : ℕ → Ty → Conv → Conv
  substAnn X S (id A)    = id (closeAt X S A)
  substAnn X S (ĉ ∷ᶜ c) = substAnnElt X S ĉ ∷ᶜ substAnn X S c

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
    all (revTy (suc X) (⇑ᵃ α) (renameᵗ suc S) A) ∷ᶜ id (closeAt X S (`∀ A))

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
    all (concTy (suc X) (⇑ᵃ α) (renameᵗ suc S) A) ∷ᶜ id (`∀ A)

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
fuse : ConvElt → ConvElt → Maybe (List ConvElt)
fuse (seal X α) (unseal Y β) with α ≟ᵃ β
fuse (seal X α) (unseal Y β) | yes _ = just []
fuse (seal X α) (unseal Y β) | no  _ = nothing
fuse (unseal X α) (seal Y β) with α ≟ᵃ β
fuse (unseal X α) (seal Y β) | yes _ = just []
fuse (unseal X α) (seal Y β) | no  _ = nothing
fuse (hide X α) (show Y β) with α ≟ᵃ β
fuse (hide X α) (show Y β) | yes _ = just []
fuse (hide X α) (show Y β) | no  _ = nothing
fuse (show X α) (hide Y β) with α ≟ᵃ β
fuse (show X α) (hide Y β) | yes _ = just []
fuse (show X α) (hide Y β) | no  _ = nothing
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
    conv-unseal : Σ ∣ Γᵢ ∋r α := R → Σ ∣ Γₑ ⊢ R ⇓ A
      → Γᵢ ▷ X := α ⇒ Γₑ
      → Σ ∣ Γᵢ ⊢̂ unseal X α ∶ ` X ⇝ A ⊣ Γₑ
    -- An identity crossing is "the same type" in named notation; in de
    -- Bruijn form the crossed assignment inserts a name entry at depth
    -- X, so the assigned side reads the type through `shiftAtᵗ X`.
    conv-hide : Γᵢ ⊢ᵗ A → Σ ∣ Γᵢ ∋a α
      → Γₑ ▷ X := α ⇒ Γᵢ
      → Σ ∣ Γᵢ ⊢̂ hide X α ∶ A ⇝ renameᵗ (shiftAtᵗ X) A ⊣ Γₑ
    conv-show : Γₑ ⊢ᵗ A
      → Γᵢ ▷ X := α ⇒ Γₑ
      → Σ ∣ Γᵢ ⊢̂ show X α ∶ renameᵗ (shiftAtᵗ X) A ⇝ A ⊣ Γₑ
    conv-fun : Σ ∣ Γₑ ⊢ s ∶ C ⇝ A ⊣ Γᵢ → Σ ∣ Γᵢ ⊢ t ∶ B ⇝ D ⊣ Γₑ
      → Σ ∣ Γᵢ ⊢̂ (s ↦ t) ∶ A ⇒ B ⇝ C ⇒ D ⊣ Γₑ
    conv-all : Σ ∣ (bind ∷ Γᵢ) ⊢ s ∶ A ⇝ B ⊣ (bind ∷ Γₑ)
      → Σ ∣ Γᵢ ⊢̂ all s ∶ `∀ A ⇝ `∀ B ⊣ Γₑ

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
all⁺ (hide X α)   = just (hide (suc X) (⇑ᵃ α) ∷ [])
all⁺ (show X α)   = just (show (suc X) (⇑ᵃ α) ∷ [])
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

-- `arr` takes the INTERIOR domain A₀ from the λ annotation at its use
-- site: the contravariant component terminates at A₀, in its own
-- coordinates, so no renaming is involved.
-- Assembled from the two scrutinees by a plain function, so that a
-- proof that knows them can REWRITE (the `with` form is stuck).
arrFrom : Ty → Maybe (List ConvElt × List ConvElt) → Ty → Maybe (Conv × Conv)
arrFrom A₀ (just (Ls , Rs)) (C ⇒ D) = just (attach Ls A₀ , attach Rs D)
arrFrom A₀ (just p) (` X) = nothing
arrFrom A₀ (just p) `ℕ = nothing
arrFrom A₀ (just p) `𝔹 = nothing
arrFrom A₀ (just p) (`∀ B) = nothing
arrFrom A₀ nothing T = nothing

arr : Ty → Conv → Maybe (Conv × Conv)
arr A₀ c = arrFrom A₀ (arrElts (elts c)) (target c)

allFrom : Maybe (List ConvElt) → Ty → Maybe Conv
allFrom (just Es) (`∀ B) = just (attach Es B)
allFrom (just Es) (` X) = nothing
allFrom (just Es) `ℕ = nothing
allFrom (just Es) `𝔹 = nothing
allFrom (just Es) (C ⇒ D) = nothing
allFrom nothing T = nothing

allView : Conv → Maybe Conv
allView c = allFrom (allElts (elts c)) (target c)

-- `base` is the view `Const` uses: a literal ignores identity
-- crossings.
base : Conv → Maybe Ty
base (id `ℕ) = just `ℕ
base (id `𝔹) = just `𝔹
base (id (` X)) = nothing
base (id (A ⇒ B)) = nothing
base (id (`∀ A)) = nothing
base (hide X α ∷ᶜ c) = base c
base (show X α ∷ᶜ c) = base c
base (seal X α ∷ᶜ c) = nothing
base (unseal X α ∷ᶜ c) = nothing
base ((s ↦ t) ∷ᶜ c) = nothing
base (all s ∷ᶜ c) = nothing

------------------------------------------------------------------------
-- Address substitution over conversions (binder discharge at `Alloc`)
------------------------------------------------------------------------

mutual
  substAddrElt : SubstAddr → ConvElt → ConvElt
  substAddrElt σ (seal X α)   = seal X (substAddr σ α)
  substAddrElt σ (unseal X α) = unseal X (substAddr σ α)
  substAddrElt σ (hide X α)   = hide X (substAddr σ α)
  substAddrElt σ (show X α)   = show X (substAddr σ α)
  substAddrElt σ (s ↦ t)    = substAddrConv σ s ↦ substAddrConv σ t
  substAddrElt σ (all s)    = all (substAddrConv (extsᵃ σ) s)

  substAddrConv : SubstAddr → Conv → Conv
  substAddrConv σ (id A)    = id A
  substAddrConv σ (ĉ ∷ᶜ c) = substAddrElt σ ĉ ∷ᶜ substAddrConv σ c

-- Pushing and popping the assignment NAMED X.  The name says how many
-- name entries stand above it — exactly what the pop judgment counts —
-- and descending past a `∀` element's binder takes the address out of
-- that binder's coordinates.  The clauses split on the CONTEXT first so
-- that both functions reduce with a variable name, which proof.Interior
-- needs.

underJust : (Ctxᵗ → Ctxᵗ) → Maybe Ctxᵗ → Maybe Ctxᵗ
underJust f (just Γ) = just (f Γ)
underJust f nothing  = nothing

pushNil : ℕ → Addr → Maybe Ctxᵗ
pushNil zero α = just (asgn α ∷ [])
pushNil (suc X) α = nothing

pushOnTop : ℕ → Addr → Ctxᵗ → Maybe Ctxᵗ
pushOnTop zero α Γ = just (asgn α ∷ Γ)
pushOnTop (suc X) α Γ = nothing

mutual
  pushAsgn : ℕ → Addr → Ctxᵗ → Maybe Ctxᵗ
  pushAsgn X α [] = pushNil X α
  pushAsgn X α (asgn β ∷ Γ) = pushOverAsgn X α β Γ
  pushAsgn X α (bind ∷ Γ) = pushOverBind X α Γ
  pushAsgn X α (addr ∷ Γ) = pushOnTop X α (addr ∷ Γ)
  pushAsgn X α (nuBind R ∷ Γ) = pushOnTop X α (nuBind R ∷ Γ)

  pushOverAsgn : ℕ → Addr → Addr → Ctxᵗ → Maybe Ctxᵗ
  pushOverAsgn zero α β Γ = just (asgn α ∷ asgn β ∷ Γ)
  pushOverAsgn (suc X) α β Γ = underJust (asgn β ∷_) (pushAsgn X α Γ)

  pushOverBind : ℕ → Addr → Ctxᵗ → Maybe Ctxᵗ
  pushOverBind zero α Γ = just (asgn α ∷ bind ∷ Γ)
  pushOverBind (suc X) (lvl ℓ) Γ = underJust (bind ∷_) (pushAsgn X (lvl ℓ) Γ)
  pushOverBind (suc X) (bnd zero) Γ = nothing
  pushOverBind (suc X) (bnd (suc i)) Γ =
    underJust (bind ∷_) (pushAsgn X (bnd i) Γ)

mutual
  popAsgn : ℕ → Addr → Ctxᵗ → Maybe Ctxᵗ
  popAsgn X α [] = nothing
  popAsgn X α (asgn β ∷ Γ) = popTop X α β Γ
  popAsgn X α (bind ∷ Γ) = popUnderBind X α Γ
  popAsgn X α (addr ∷ Γ) = nothing
  popAsgn X α (nuBind R ∷ Γ) = nothing

  popTop : ℕ → Addr → Addr → Ctxᵗ → Maybe Ctxᵗ
  popTop zero α β Γ with α ≟ᵃ β
  popTop zero α β Γ | yes _ = just Γ
  popTop zero α β Γ | no _ = nothing
  popTop (suc X) α β Γ = nothing

  popUnderBind : ℕ → Addr → Ctxᵗ → Maybe Ctxᵗ
  popUnderBind zero α Γ = nothing
  popUnderBind (suc X) (lvl ℓ) Γ = underJust (bind ∷_) (popAsgn X (lvl ℓ) Γ)
  popUnderBind (suc X) (bnd zero) Γ = nothing
  popUnderBind (suc X) (bnd (suc i)) Γ =
    underJust (bind ∷_) (popAsgn X (bnd i) Γ)


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
  interiorElt (all s)      Γ with interior s (bind ∷ Γ)
  interiorElt (all s)      Γ | just (bind ∷ Γ′) = just Γ′
  interiorElt (all s)      Γ | just (addr ∷ Γ′) = nothing
  interiorElt (all s)      Γ | just (nuBind R ∷ Γ′) = nothing
  interiorElt (all s)      Γ | just (asgn β ∷ Γ′) = nothing
  interiorElt (all s)      Γ | just [] = nothing
  interiorElt (all s)      Γ | nothing = nothing

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
