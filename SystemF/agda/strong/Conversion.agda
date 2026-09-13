module strong.Conversion where

-- Strong System F v7 — normal-form lists of conversion heads.

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (_≟_; _<?_)
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; substᵗ; renameᵗ; extᵗ)
open import strong.RepresentationTypes using (Anchor; Renameᴿ; extᴿ)
open import strong.Ctx

------------------------------------------------------------------------
-- Syntax
------------------------------------------------------------------------

mutual
  data Head : Set where
    seal   : Anchor → Head
    unseal : Anchor → Head
    _↦_    : Conv → Conv → Head
    all    : Conv → Head

  data Conv : Set where
    id  : Ty → Conv
    _∷ᶜ_ : Head → Conv → Conv

infixr 7 _↦_
infixr 6 _∷ᶜ_

mutual
  renHead : Renameᵗ → Renameᴿ → Head → Head
  renHead ρ σ (seal α)   = seal (σ α)
  renHead ρ σ (unseal α) = unseal (σ α)
  renHead ρ σ (c ↦ d)    = renConv ρ σ c ↦ renConv ρ σ d
  renHead ρ σ (all c)    = all (renConv (extᵗ ρ) (extᴿ σ) c)

  renConv : Renameᵗ → Renameᴿ → Conv → Conv
  renConv ρ σ (id A)   = id (renameᵗ ρ A)
  renConv ρ σ (h ∷ᶜ c) = renHead ρ σ h ∷ᶜ renConv ρ σ c

heads : Conv → List Head
heads (id A)   = []
heads (h ∷ᶜ c) = h ∷ heads c

target : Conv → Ty
target (id A)   = A
target (h ∷ᶜ c) = target c

attach : List Head → Ty → Conv
attach []       A = id A
attach (h ∷ hs) A = h ∷ᶜ attach hs A

------------------------------------------------------------------------
-- Type-variable closing and canonical conversions
------------------------------------------------------------------------

closeEnv : ℕ → Ty → ℕ → Ty
closeEnv X S Y with X ≟ Y
closeEnv X S Y | yes _ = S
closeEnv X S Y | no _ with X <? Y
closeEnv X S Y | no _ | yes _ = ` (Y ∸ 1)
closeEnv X S Y | no _ | no  _ = ` Y

closeAt : ℕ → Ty → Ty → Ty
closeAt X S A = substᵗ (closeEnv X S) A

mutual
  revTy : ℕ → Anchor → Ty → Ty → Conv
  revTy X α S (` Y) with X ≟ Y
  revTy X α S (` Y) | yes _ = unseal α ∷ᶜ id S
  revTy X α S (` Y) | no  _ = id (closeAt X S (` Y))
  revTy X α S `ℕ      = id `ℕ
  revTy X α S `𝔹      = id `𝔹
  revTy X α S (A ⇒ B) =
    (concTy X α S A ↦ revTy X α S B) ∷ᶜ id (closeAt X S (A ⇒ B))
  revTy X α S (`∀ A)  =
    all (revTy (suc X) (suc α) (renameᵗ suc S) A)
      ∷ᶜ id (closeAt X S (`∀ A))

  concTy : ℕ → Anchor → Ty → Ty → Conv
  concTy X α S (` Y) with X ≟ Y
  concTy X α S (` Y) | yes _ = seal α ∷ᶜ id (` X)
  concTy X α S (` Y) | no  _ = id (` Y)
  concTy X α S `ℕ      = id `ℕ
  concTy X α S `𝔹      = id `𝔹
  concTy X α S (A ⇒ B) =
    (revTy X α S A ↦ concTy X α S B) ∷ᶜ id (A ⇒ B)
  concTy X α S (`∀ A)  =
    all (concTy (suc X) (suc α) (renameᵗ suc S) A) ∷ᶜ id (`∀ A)

------------------------------------------------------------------------
-- Normalizing composition
------------------------------------------------------------------------

mutual
  weightHead : Head → ℕ
  weightHead (seal α)   = 1
  weightHead (unseal α) = 1
  weightHead (c ↦ d)    = suc (weight c + weight d)
  weightHead (all c)    = suc (weight c)

  weight : Conv → ℕ
  weight (id A)   = 1
  weight (h ∷ᶜ c) = suc (weightHead h + weight c)

weightHeads : List Head → ℕ
weightHeads []       = zero
weightHeads (h ∷ hs) = weightHead h + weightHeads hs

-- Appending two conversions: the first one's terminator gives way to the
-- second.  This is the RAW composition; the normalizing one is
-- `strong.ConversionReduction._⨟_`, which appends and then reduces the
-- adjacent-pair redexes to a normal form.
infixl 5 _⧺_
_⧺_ : Conv → Conv → Conv
id A ⧺ d      = d
(h ∷ᶜ c) ⧺ d = h ∷ᶜ (c ⧺ d)

-- One adjacent pair of heads fuses — or does not, and `nothing` here is
-- what the normal form `NF` forbids.  A `↦` or `all` fusion defers its
-- component compositions as plain APPENDS; the reduction system's
-- congruence steps finish them.  No fuel: every clause is structural.
fuse : Head → Head → Maybe (List Head)
fuse (seal α) (unseal β) with α ≟ β
fuse (seal α) (unseal β) | yes _ = just []
fuse (seal α) (unseal β) | no  _ = nothing
fuse (unseal α) (seal β) with α ≟ β
fuse (unseal α) (seal β) | yes _ = just []
fuse (unseal α) (seal β) | no  _ = nothing
fuse (s₁ ↦ t₁) (s₂ ↦ t₂) = just (((s₂ ⧺ s₁) ↦ (t₁ ⧺ t₂)) ∷ [])
fuse (all s) (all t) = just (all (s ⧺ t) ∷ [])
fuse (seal α) (seal β) = nothing
fuse (seal α) (c ↦ d) = nothing
fuse (seal α) (all c) = nothing
fuse (unseal α) (unseal β) = nothing
fuse (unseal α) (c ↦ d) = nothing
fuse (unseal α) (all c) = nothing
fuse (c ↦ d) (seal β) = nothing
fuse (c ↦ d) (unseal β) = nothing
fuse (c ↦ d) (all e) = nothing
fuse (all c) (seal β) = nothing
fuse (all c) (unseal β) = nothing
fuse (all c) (c′ ↦ d′) = nothing

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------
--
-- THE SEAM CONDITION.  Every context along a conversion binds the same
-- ANCHORS, and differs only in which of them are revealed: a scope change
-- flips visibility bits and adds no entry.  The rules record the shadow of
-- that which the metatheory consumes — `anchorCount Δ₁ ≡ anchorCount Δ₂`
-- on the three rules that do not already inherit it (`conv-fun` inherits
-- from its swapped pair, `conv-all` by injectivity, `conv-cons` by
-- transitivity through its seam).
--
-- With merged entries this no longer guards `SameTy`, which now matches
-- free variables by anchor INDEX; it is what ANCHOR WEAKENING consumes,
-- since `renConv` applies ONE renaming to a whole conversion and every
-- context in its chain must therefore admit the same insertion.  See
-- notes/DECISIONS.md (2026-09-13).

private
  variable
    Δ₁ Δ₂ Δ₃ : Ctxᵗ
    A B C D : Ty
    R : strong.RepresentationTypes.RepTy
    X : ℕ
    α : Anchor
    c d : Conv
    h : Head

infix 4 _⊢̂_∶_⇝_⊣_
infix 4 _⊢_∶_⇝_⊣_
infix 4 _⊩_∶_⇝_⊣_
mutual
  data _⊢̂_∶_⇝_⊣_ : Ctxᵗ → Head → Ty → Ty → Ctxᵗ → Set where
    conv-seal : ∀ {S}
      → Δ₂ ∋n X := α → Δ₂ ∋r α := R → Δ₁ ⊢ R ⇓ S
      → anchorCount Δ₁ ≡ anchorCount Δ₂
      → Δ₁ ⊢̂ seal α ∶ S ⇝ ` X ⊣ Δ₂
    conv-unseal : ∀ {S}
      → Δ₁ ∋n X := α → Δ₁ ∋r α := R → Δ₂ ⊢ R ⇓ S
      → anchorCount Δ₁ ≡ anchorCount Δ₂
      → Δ₁ ⊢̂ unseal α ∶ ` X ⇝ S ⊣ Δ₂
    conv-fun : ∀ {s t A′ B′}
      → Δ₂ ⊢ s ∶ A′ ⇝ A ⊣ Δ₁ → Δ₁ ⊢ t ∶ B ⇝ B′ ⊣ Δ₂
      → Δ₁ ⊢̂ s ↦ t ∶ A ⇒ B ⇝ A′ ⇒ B′ ⊣ Δ₂
    conv-all : ∀ {s}
      → (anch revealed abstA ∷ Δ₁) ⊢ s ∶ A ⇝ B
          ⊣ (anch revealed abstA ∷ Δ₂)
      → Δ₁ ⊢̂ all s ∶ `∀ A ⇝ `∀ B ⊣ Δ₂

  data _⊢_∶_⇝_⊣_ : Ctxᵗ → Conv → Ty → Ty → Ctxᵗ → Set where
    conv-id : SameTy zero Δ₁ A Δ₂ B
      → anchorCount Δ₁ ≡ anchorCount Δ₂
      → Δ₁ ⊢ id B ∶ A ⇝ B ⊣ Δ₂
    conv-cons : Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → Δ₂ ⊩ c ∶ B ⇝ C ⊣ Δ₃
      → Δ₁ ⊢ h ∷ᶜ c ∶ A ⇝ C ⊣ Δ₃

  -- A conversion TAIL.  Its terminator is REFLEXIVE: same context, same
  -- type, `sameTy-refl`.  All BRIDGING between two indexings therefore
  -- happens in a BARE `id`, never in a terminator — which is what pins a
  -- cons's last seam to the exterior, and so what lets `arr` and
  -- `allView`, which read the syntax, return correctly typed components.
  -- Every conversion the builders produce already satisfies this:
  -- `revTy`/`concTy` terminate at `Δₑ ⊣ Δₑ`.
  data _⊩_∶_⇝_⊣_ : Ctxᵗ → Conv → Ty → Ty → Ctxᵗ → Set where
    tail-id : Δ₁ ⊢ᵗ A → Δ₁ ⊩ id A ∶ A ⇝ A ⊣ Δ₁
    tail-cons : Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → Δ₂ ⊩ c ∶ B ⇝ C ⊣ Δ₃
      → Δ₁ ⊩ h ∷ᶜ c ∶ A ⇝ C ⊣ Δ₃

------------------------------------------------------------------------
-- Normal forms and views
------------------------------------------------------------------------

mutual
  data NFHead : Head → Set where
    nf-seal   : NFHead (seal α)
    nf-unseal : NFHead (unseal α)
    nf-fun    : NF c → NF d → NFHead (c ↦ d)
    nf-all    : NF c → NFHead (all c)

  data IrreducibleAfter (h : Head) : Conv → Set where
    irr-id   : ∀ {A} → IrreducibleAfter h (id A)
    irr-cons : ∀ {k c} → fuse h k ≡ nothing
             → IrreducibleAfter h (k ∷ᶜ c)

  data NF : Conv → Set where
    nf-id   : ∀ {A} → NF (id A)
    nf-cons : NFHead h → NF c → IrreducibleAfter h c → NF (h ∷ᶜ c)

-- `arr` splits a conversion at an arrow type into its two components.
-- The contravariant component must END at the INTERIOR's domain — a type
-- the conversion's syntax does not carry when the conversion is a bare
-- `id`, since `id` names its target.  In the notes' named setting the two
-- domains are literally the same type, so `arr(id(A → B)) = (id A , id B)`
-- is unambiguous there; here the interior domain is an ARGUMENT, supplied
-- by the `ƛ` that canonical forms place inside every arrow-typed boundary.
arr : Ty → Conv → Maybe (Conv × Conv)
arr A₁ (id (A ⇒ B))             = just (id A₁ , id B)
arr A₁ ((c ↦ d) ∷ᶜ id (A ⇒ B)) = just (c , d)
arr A₁ _                         = nothing

allView : Conv → Maybe Conv
allView (id (`∀ A))         = just (id A)
allView (all c ∷ᶜ id (`∀ A)) = just c
allView _                    = nothing
