module strong.Conversion where

-- Strong System F v8 — conversions: lists of conversion elements.
--
-- The four atomic elements each cross the introduction of one name
-- assignment, and each carries its ADDRESS:
--
--   seal α     seal{-X:=α}    : A ⇝ X    renames via α's representation
--   unseal α   unseal{+X:=α}  : X ⇝ A
--   hide α     id{-X:=α}      : A ⇝ A    identity conceal crossing
--   show α     id{+X:=α}      : A ⇝ A    identity reveal crossing
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
    seal   : Addr → ConvElt
    unseal : Addr → ConvElt
    hide   : Addr → ConvElt
    show   : Addr → ConvElt
    _↦_    : Conv → Conv → ConvElt
    all    : Conv → ConvElt

  data Conv : Set where
    id   : Ty → Conv
    _∷ᶜ_ : ConvElt → Conv → Conv

infixr 7 _↦_
infixr 6 _∷ᶜ_

mutual
  renElt : Renameᵗ → Renameᵇ → ConvElt → ConvElt
  renElt ρ σ (seal α)   = seal (renᵃ σ α)
  renElt ρ σ (unseal α) = unseal (renᵃ σ α)
  renElt ρ σ (hide α)   = hide (renᵃ σ α)
  renElt ρ σ (show α)   = show (renᵃ σ α)
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

-- c[X:=S]: substitution on the type annotations only; the elements are
-- untouched, so the crossings a conversion performs are unchanged.
mutual
  substAnnElt : ℕ → Ty → ConvElt → ConvElt
  substAnnElt X S (seal α)   = seal α
  substAnnElt X S (unseal α) = unseal α
  substAnnElt X S (hide α)   = hide α
  substAnnElt X S (show α)   = show α
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
  revTy X α S (` Y) | yes _ = unseal α ∷ᶜ id S
  revTy X α S (` Y) | no  _ = show α ∷ᶜ id (closeAt X S (` Y))
  revTy X α S `ℕ = show α ∷ᶜ id `ℕ
  revTy X α S `𝔹 = show α ∷ᶜ id `𝔹
  revTy X α S (A ⇒ B) with occursᵗ X (A ⇒ B)
  revTy X α S (A ⇒ B) | false = show α ∷ᶜ id (closeAt X S (A ⇒ B))
  revTy X α S (A ⇒ B) | true =
    (concTy X α S A ↦ revTy X α S B) ∷ᶜ id (closeAt X S (A ⇒ B))
  revTy X α S (`∀ A) with occursᵗ (suc X) A
  revTy X α S (`∀ A) | false = show α ∷ᶜ id (closeAt X S (`∀ A))
  revTy X α S (`∀ A) | true =
    all (revTy (suc X) (⇑ᵃ α) (renameᵗ suc S) A) ∷ᶜ id (closeAt X S (`∀ A))

  concTy : ℕ → Addr → Ty → Ty → Conv
  concTy X α S (` Y) with X ≟ Y
  concTy X α S (` Y) | yes _ = seal α ∷ᶜ id (` X)
  concTy X α S (` Y) | no  _ = hide α ∷ᶜ id (` Y)
  concTy X α S `ℕ = hide α ∷ᶜ id `ℕ
  concTy X α S `𝔹 = hide α ∷ᶜ id `𝔹
  concTy X α S (A ⇒ B) with occursᵗ X (A ⇒ B)
  concTy X α S (A ⇒ B) | false = hide α ∷ᶜ id (A ⇒ B)
  concTy X α S (A ⇒ B) | true =
    (revTy X α S A ↦ concTy X α S B) ∷ᶜ id (A ⇒ B)
  concTy X α S (`∀ A) with occursᵗ (suc X) A
  concTy X α S (`∀ A) | false = hide α ∷ᶜ id (`∀ A)
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
fuse (seal α) (unseal β) with α ≟ᵃ β
fuse (seal α) (unseal β) | yes _ = just []
fuse (seal α) (unseal β) | no  _ = nothing
fuse (unseal α) (seal β) with α ≟ᵃ β
fuse (unseal α) (seal β) | yes _ = just []
fuse (unseal α) (seal β) | no  _ = nothing
fuse (hide α) (show β) with α ≟ᵃ β
fuse (hide α) (show β) | yes _ = just []
fuse (hide α) (show β) | no  _ = nothing
fuse (show α) (hide β) with α ≟ᵃ β
fuse (show α) (hide β) | yes _ = just []
fuse (show α) (hide β) | no  _ = nothing
fuse (s₁ ↦ t₁) (s₂ ↦ t₂) = just (((s₂ ⧺ s₁) ↦ (t₁ ⧺ t₂)) ∷ [])
fuse (all s) (all t) = just (all (s ⧺ t) ∷ [])
fuse (seal α) (seal β) = nothing
fuse (seal α) (hide β) = nothing
fuse (seal α) (show β) = nothing
fuse (seal α) (s ↦ t) = nothing
fuse (seal α) (all s) = nothing
fuse (unseal α) (unseal β) = nothing
fuse (unseal α) (hide β) = nothing
fuse (unseal α) (show β) = nothing
fuse (unseal α) (s ↦ t) = nothing
fuse (unseal α) (all s) = nothing
fuse (hide α) (seal β) = nothing
fuse (hide α) (unseal β) = nothing
fuse (hide α) (hide β) = nothing
fuse (hide α) (s ↦ t) = nothing
fuse (hide α) (all s) = nothing
fuse (show α) (seal β) = nothing
fuse (show α) (unseal β) = nothing
fuse (show α) (show β) = nothing
fuse (show α) (s ↦ t) = nothing
fuse (show α) (all s) = nothing
fuse (s ↦ t) (seal β) = nothing
fuse (s ↦ t) (unseal β) = nothing
fuse (s ↦ t) (hide β) = nothing
fuse (s ↦ t) (show β) = nothing
fuse (s ↦ t) (all u) = nothing
fuse (all s) (seal β) = nothing
fuse (all s) (unseal β) = nothing
fuse (all s) (hide β) = nothing
fuse (all s) (show β) = nothing
fuse (all s) (t ↦ u) = nothing

mutual
  weightElt : ConvElt → ℕ
  weightElt (seal α)   = 1
  weightElt (unseal α) = 1
  weightElt (hide α)   = 1
  weightElt (show α)   = 1
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
      → Σ ∣ Γᵢ ⊢̂ seal α ∶ A ⇝ ` X ⊣ Γₑ
    conv-unseal : Σ ∣ Γᵢ ∋r α := R → Σ ∣ Γₑ ⊢ R ⇓ A
      → Γᵢ ▷ X := α ⇒ Γₑ
      → Σ ∣ Γᵢ ⊢̂ unseal α ∶ ` X ⇝ A ⊣ Γₑ
    -- An identity crossing is "the same type" in named notation; in de
    -- Bruijn form the crossed assignment inserts a name entry at depth
    -- X, so the assigned side reads the type through `shiftAtᵗ X`.
    conv-hide : Γᵢ ⊢ᵗ A → Σ ∣ Γᵢ ∋a α
      → Γₑ ▷ X := α ⇒ Γᵢ
      → Σ ∣ Γᵢ ⊢̂ hide α ∶ A ⇝ renameᵗ (shiftAtᵗ X) A ⊣ Γₑ
    conv-show : Γₑ ⊢ᵗ A
      → Γᵢ ▷ X := α ⇒ Γₑ
      → Σ ∣ Γᵢ ⊢̂ show α ∶ renameᵗ (shiftAtᵗ X) A ⇝ A ⊣ Γₑ
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
    nf-seal   : ∀ {α} → NFElt (seal α)
    nf-unseal : ∀ {α} → NFElt (unseal α)
    nf-hide   : ∀ {α} → NFElt (hide α)
    nf-show   : ∀ {α} → NFElt (show α)
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
arr⁻ (seal α)   = nothing
arr⁻ (unseal α) = nothing
arr⁻ (hide α)   = just (show α ∷ [])
arr⁻ (show α)   = just (hide α ∷ [])
arr⁻ (s ↦ t)    = just (elts s)
arr⁻ (all s)    = nothing

arr⁺ : ConvElt → Maybe (List ConvElt)
arr⁺ (seal α)   = nothing
arr⁺ (unseal α) = nothing
arr⁺ (hide α)   = just (hide α ∷ [])
arr⁺ (show α)   = just (show α ∷ [])
arr⁺ (s ↦ t)    = just (elts t)
arr⁺ (all s)    = nothing

-- A hoisted crossing moves under the ∀ element's binder, so its bound
-- address shifts; `arr` introduces no binder, so `arr⁻`/`arr⁺` do not.
all⁺ : ConvElt → Maybe (List ConvElt)
all⁺ (seal α)   = nothing
all⁺ (unseal α) = nothing
all⁺ (hide α)   = just (hide (⇑ᵃ α) ∷ [])
all⁺ (show α)   = just (show (⇑ᵃ α) ∷ [])
all⁺ (s ↦ t)    = nothing
all⁺ (all s)    = just (elts s)

-- Fold over the element list; the contravariant side reverses.
arrElts : List ConvElt → Maybe (List ConvElt × List ConvElt)
arrElts [] = just ([] , [])
arrElts (ĉ ∷ ĉs) with arr⁻ ĉ | arr⁺ ĉ | arrElts ĉs
arrElts (ĉ ∷ ĉs) | just ls | just rs | just (Ls , Rs) =
  just (Ls ++ ls , rs ++ Rs)
arrElts (ĉ ∷ ĉs) | nothing | _ | _ = nothing
arrElts (ĉ ∷ ĉs) | just ls | nothing | _ = nothing
arrElts (ĉ ∷ ĉs) | just ls | just rs | nothing = nothing

allElts : List ConvElt → Maybe (List ConvElt)
allElts [] = just []
allElts (ĉ ∷ ĉs) with all⁺ ĉ | allElts ĉs
allElts (ĉ ∷ ĉs) | just es | just Es = just (es ++ Es)
allElts (ĉ ∷ ĉs) | nothing | _ = nothing
allElts (ĉ ∷ ĉs) | just es | nothing = nothing

-- `arr` takes the INTERIOR domain A₀ from the λ annotation at its use
-- site: the contravariant component terminates at A₀, in its own
-- coordinates, so no renaming is involved.
arr : Ty → Conv → Maybe (Conv × Conv)
arr A₀ c with target c | arrElts (elts c)
arr A₀ c | C ⇒ D | just (Ls , Rs) = just (attach Ls A₀ , attach Rs D)
arr A₀ c | C ⇒ D | nothing = nothing
arr A₀ c | ` X | _ = nothing
arr A₀ c | `ℕ | _ = nothing
arr A₀ c | `𝔹 | _ = nothing
arr A₀ c | `∀ B | _ = nothing

allView : Conv → Maybe Conv
allView c with target c | allElts (elts c)
allView c | `∀ B | just Es = just (attach Es B)
allView c | `∀ B | nothing = nothing
allView c | ` X | _ = nothing
allView c | `ℕ | _ = nothing
allView c | `𝔹 | _ = nothing
allView c | C ⇒ D | _ = nothing

-- `base` is the view `Const` uses: a literal ignores identity
-- crossings.
base : Conv → Maybe Ty
base (id `ℕ) = just `ℕ
base (id `𝔹) = just `𝔹
base (id (` X)) = nothing
base (id (A ⇒ B)) = nothing
base (id (`∀ A)) = nothing
base (hide α ∷ᶜ c) = base c
base (show α ∷ᶜ c) = base c
base (seal α ∷ᶜ c) = nothing
base (unseal α ∷ᶜ c) = nothing
base ((s ↦ t) ∷ᶜ c) = nothing
base (all s ∷ᶜ c) = nothing

------------------------------------------------------------------------
-- Address substitution over conversions (binder discharge at `Alloc`)
------------------------------------------------------------------------

mutual
  substAddrElt : SubstAddr → ConvElt → ConvElt
  substAddrElt σ (seal α)   = seal (substAddr σ α)
  substAddrElt σ (unseal α) = unseal (substAddr σ α)
  substAddrElt σ (hide α)   = hide (substAddr σ α)
  substAddrElt σ (show α)   = show (substAddr σ α)
  substAddrElt σ (s ↦ t)    = substAddrConv σ s ↦ substAddrConv σ t
  substAddrElt σ (all s)    = all (substAddrConv (extsᵃ σ) s)

  substAddrConv : SubstAddr → Conv → Conv
  substAddrConv σ (id A)    = id A
  substAddrConv σ (ĉ ∷ᶜ c) = substAddrElt σ ĉ ∷ᶜ substAddrConv σ c

------------------------------------------------------------------------
-- The interior context of a conversion: `⟨c⟩(Γ)` as a partial function,
-- walking the elements from the terminator inward
------------------------------------------------------------------------

popAt : Addr → Ctxᵗ → Maybe Ctxᵗ
popAt α [] = nothing
popAt α (asgn β ∷ Γ) with α ≟ᵃ β
popAt α (asgn β ∷ Γ) | yes _ = just Γ
popAt α (asgn β ∷ Γ) | no _ = nothing
popAt (bnd zero) (bind ∷ Γ) = nothing
popAt (bnd (suc i)) (bind ∷ Γ) with popAt (bnd i) Γ
popAt (bnd (suc i)) (bind ∷ Γ) | just Γ′ = just (bind ∷ Γ′)
popAt (bnd (suc i)) (bind ∷ Γ) | nothing = nothing
popAt (lvl ℓ) (bind ∷ Γ) with popAt (lvl ℓ) Γ
popAt (lvl ℓ) (bind ∷ Γ) | just Γ′ = just (bind ∷ Γ′)
popAt (lvl ℓ) (bind ∷ Γ) | nothing = nothing
popAt (bnd zero) (addr ∷ Γ) = nothing
popAt (bnd (suc i)) (addr ∷ Γ) with popAt (bnd i) Γ
popAt (bnd (suc i)) (addr ∷ Γ) | just Γ′ = just (addr ∷ Γ′)
popAt (bnd (suc i)) (addr ∷ Γ) | nothing = nothing
popAt (lvl ℓ) (addr ∷ Γ) with popAt (lvl ℓ) Γ
popAt (lvl ℓ) (addr ∷ Γ) | just Γ′ = just (addr ∷ Γ′)
popAt (lvl ℓ) (addr ∷ Γ) | nothing = nothing
popAt (bnd zero) (nuBind R ∷ Γ) = nothing
popAt (bnd (suc i)) (nuBind R ∷ Γ) with popAt (bnd i) Γ
popAt (bnd (suc i)) (nuBind R ∷ Γ) | just Γ′ = just (nuBind R ∷ Γ′)
popAt (bnd (suc i)) (nuBind R ∷ Γ) | nothing = nothing
popAt (lvl ℓ) (nuBind R ∷ Γ) with popAt (lvl ℓ) Γ
popAt (lvl ℓ) (nuBind R ∷ Γ) | just Γ′ = just (nuBind R ∷ Γ′)
popAt (lvl ℓ) (nuBind R ∷ Γ) | nothing = nothing

mutual
  interiorElt : ConvElt → Ctxᵗ → Maybe Ctxᵗ
  interiorElt (seal α)   Γ = popAt α Γ
  interiorElt (hide α)   Γ = popAt α Γ
  interiorElt (unseal α) Γ = just (asgn α ∷ Γ)
  interiorElt (show α)   Γ = just (asgn α ∷ Γ)
  interiorElt (s ↦ t)    Γ = interior t Γ
  interiorElt (all s)    Γ with interior s (bind ∷ Γ)
  interiorElt (all s)    Γ | just (bind ∷ Γ′) = just Γ′
  interiorElt (all s)    Γ | just (addr ∷ Γ′) = nothing
  interiorElt (all s)    Γ | just (nuBind R ∷ Γ′) = nothing
  interiorElt (all s)    Γ | just (asgn β ∷ Γ′) = nothing
  interiorElt (all s)    Γ | just [] = nothing
  interiorElt (all s)    Γ | nothing = nothing

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
