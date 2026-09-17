module strong.RepresentationTypes where

-- Strong System F v8 — representation types and their ADDRESSES.
--
-- Two forms, and the distinction is DE BRUIJN LEVEL versus DE BRUIJN
-- INDEX — they are counted from opposite ends, and that is why they
-- cannot be one `ℕ`:
--
--   lvl ℓ   a LEVEL into the global store, counted from the bottom.
--           The store is append-only, so a level is permanent and no
--           renaming touches it.
--   bse j   an INDEX into the base, counted from the newest binder.
--           A `Λ` or a `ν` pushes one, and that push shifts every `bse`.
--
-- Each convention is forced.  The store must use levels because it is
-- shared: with indices, every `Alloc` would renumber every stored
-- address in every term.  The base must use indices because `crossΛ`
-- has to WRITE the `Λ`'s address syntactically, and that is `bse 0`;
-- as a level it would be `length Bs`, which depends on the enclosing
-- telescope.  `notes/AddrNeeded` has the witness that keeping them
-- apart is load-bearing: the color wrap's `bse 0` sits next to a
-- seal's `lvl 0`, and merging them would let `fuse` cancel the two.
--
-- A `∀` binds NEITHER: it binds a type variable, `ᵛ, which is not an
-- address.  So there is exactly one address renaming — `renᵃᵉ`,
-- `renameᴿᵉ`, `renConvᵉ`, `renBseᴹ`, extending under `Λ` and `ν` — and
-- descending under a `∀` moves nothing.  Substitution has two jobs:
-- `substᴿⱽ`/`instⱽ₀` instantiate a `∀ᴿ`'s type variable,
-- `substAddrᵉ`/`instᵉ₀` a `ν`'s `bse`, to a level, at `Alloc`.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Addr : Set where
  lvl : ℕ → Addr
  bse : ℕ → Addr

lvl-inj : ∀ {ℓ m} → lvl ℓ ≡ lvl m → ℓ ≡ m
lvl-inj refl = refl

bse-inj : ∀ {i j} → bse i ≡ bse j → i ≡ j
bse-inj refl = refl

infix 4 _≟ᵃ_
_≟ᵃ_ : (α β : Addr) → Dec (α ≡ β)
lvl ℓ ≟ᵃ lvl m with ℓ ≟ m
lvl ℓ ≟ᵃ lvl m | yes refl = yes refl
lvl ℓ ≟ᵃ lvl m | no ne = no λ eq → ne (lvl-inj eq)
lvl ℓ ≟ᵃ bse j = no λ ()
bse i ≟ᵃ lvl m = no λ ()
bse i ≟ᵃ bse j with i ≟ j
bse i ≟ᵃ bse j | yes refl = yes refl
bse i ≟ᵃ bse j | no ne = no λ eq → ne (bse-inj eq)

infixr 7 _⇒ᴿ_
infix 6 `∀ᴿ

data RepTy : Set where
  `ᵃ_  : Addr → RepTy      -- a FREE address
  `ᵛ_  : ℕ → RepTy         -- a type variable bound by an enclosing ∀ᴿ
  `ℕᴿ  : RepTy
  `𝔹ᴿ  : RepTy
  _⇒ᴿ_ : RepTy → RepTy → RepTy
  `∀ᴿ  : RepTy → RepTy

------------------------------------------------------------------------
-- Renaming of BOUND addresses; levels are stable
------------------------------------------------------------------------

Renameᵇ : Set
Renameᵇ = ℕ → ℕ

-- The ONLY address renaming: a base push renumbers `bse`; a level is
-- permanent.  There is no stack-address family any more — a `∀` binds a
-- type VARIABLE, not an address, so passing one moves no address at
-- all.
renᵃᵉ : Renameᵇ → Addr → Addr
renᵃᵉ ρ (lvl ℓ) = lvl ℓ
renᵃᵉ ρ (bse j) = bse (ρ j)

⇑ᵃᵉ : Addr → Addr
⇑ᵃᵉ = renᵃᵉ suc

extᵇ : Renameᵇ → Renameᵇ
extᵇ ρ zero    = zero
extᵇ ρ (suc i) = suc (ρ i)

-- `∀ᴿ` binds a type variable, so a base renaming passes through it
-- unextended and leaves `ᵛ alone.
renameᴿᵉ : Renameᵇ → RepTy → RepTy
renameᴿᵉ ρ (`ᵃ α)   = `ᵃ renᵃᵉ ρ α
renameᴿᵉ ρ (`ᵛ i)   = `ᵛ i
renameᴿᵉ ρ `ℕᴿ      = `ℕᴿ
renameᴿᵉ ρ `𝔹ᴿ      = `𝔹ᴿ
renameᴿᵉ ρ (R ⇒ᴿ S) = renameᴿᵉ ρ R ⇒ᴿ renameᴿᵉ ρ S
renameᴿᵉ ρ (`∀ᴿ R)  = `∀ᴿ (renameᴿᵉ ρ R)

⇑ᴿᵉ : RepTy → RepTy
⇑ᴿᵉ = renameᴿᵉ suc

------------------------------------------------------------------------
-- Instantiating a `∀ᴿ`
------------------------------------------------------------------------
-- Its binder is a type VARIABLE, so instantiation replaces `ᵛ 0 by a
-- representation — at `TyBeta` that is the address of the `ν` the rule
-- creates — and the remaining bound indices shift down.

SubstAddr : Set
SubstAddr = ℕ → Addr

substᴿⱽ : (ℕ → RepTy) → RepTy → RepTy
substᴿⱽ σ (`ᵃ α)   = `ᵃ α
substᴿⱽ σ (`ᵛ i)   = σ i
substᴿⱽ σ `ℕᴿ      = `ℕᴿ
substᴿⱽ σ `𝔹ᴿ      = `𝔹ᴿ
substᴿⱽ σ (R ⇒ᴿ S) = substᴿⱽ σ R ⇒ᴿ substᴿⱽ σ S
substᴿⱽ σ (`∀ᴿ R)  = `∀ᴿ (substᴿⱽ (extsⱽ σ) R)
  where
  extsⱽ : (ℕ → RepTy) → (ℕ → RepTy)
  extsⱽ τ zero = `ᵛ zero
  extsⱽ τ (suc i) = shiftⱽ (τ i)
    where
    shiftⱽ : RepTy → RepTy
    shiftⱽ (`ᵃ α) = `ᵃ α
    shiftⱽ (`ᵛ i) = `ᵛ (suc i)
    shiftⱽ `ℕᴿ = `ℕᴿ
    shiftⱽ `𝔹ᴿ = `𝔹ᴿ
    shiftⱽ (R ⇒ᴿ S) = shiftⱽ R ⇒ᴿ shiftⱽ S
    shiftⱽ (`∀ᴿ R) = `∀ᴿ R

instⱽ₀ : Addr → (ℕ → RepTy)
instⱽ₀ β zero    = `ᵃ β
instⱽ₀ β (suc i) = `ᵛ i

infix 8 _[_]ᵇ
_[_]ᵇ : RepTy → Addr → RepTy
R [ β ]ᵇ = substᴿⱽ (instⱽ₀ β) R

------------------------------------------------------------------------
-- The BASE mirror: discharging a `ν` replaces its address by a level
------------------------------------------------------------------------

substAddrᵉ : SubstAddr → Addr → Addr
substAddrᵉ σ (lvl ℓ) = lvl ℓ
substAddrᵉ σ (bse j) = σ j

substᴿᵉ : SubstAddr → RepTy → RepTy
substᴿᵉ σ (`ᵃ α)   = `ᵃ substAddrᵉ σ α
substᴿᵉ σ (`ᵛ i)   = `ᵛ i
substᴿᵉ σ `ℕᴿ      = `ℕᴿ
substᴿᵉ σ `𝔹ᴿ      = `𝔹ᴿ
substᴿᵉ σ (R ⇒ᴿ S) = substᴿᵉ σ R ⇒ᴿ substᴿᵉ σ S
substᴿᵉ σ (`∀ᴿ R)  = `∀ᴿ (substᴿᵉ σ R)

extsᵃᵉ : SubstAddr → SubstAddr
extsᵃᵉ σ zero    = bse zero
extsᵃᵉ σ (suc j) = ⇑ᵃᵉ (σ j)

instᵉ₀ : Addr → SubstAddr
instᵉ₀ β zero    = β
instᵉ₀ β (suc j) = bse j

_[_]ᵉ : RepTy → Addr → RepTy
R [ β ]ᵉ = substᴿᵉ (instᵉ₀ β) R
