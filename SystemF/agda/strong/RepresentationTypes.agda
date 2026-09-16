module strong.RepresentationTypes where

-- Strong System F v8 — representation types and their ADDRESSES.
--
-- An address locates a representation type.  There are three forms,
-- and they are distinguished by WHO BINDS THEM:
--
--   lvl ℓ   the global store Σ.  Introduced only by `Alloc`, which
--           appends; the store never reorders or removes, so a level
--           is permanent and NEITHER renaming family touches it.
--
--   bnd i   a `∀`.  Every ∀-shaped rule pushes the stack entry `bind`
--           that binds one: `wf-∀` (types), `wfᴿ-∀` (representation
--           types), `read-∀` (read-back), `quote-∀` (`⌊·⌋`), and
--           `conv-all` (the `∀` conversion element).  All type level.
--
--   bse j   a `Λ` or a `ν`.  `⊢Λ` pushes the base entry `addr`, `⊢ν`
--           pushes `nuBind R`.  Both term level.
--
-- So the split is not two arbitrary halves: it is TYPE binders against
-- TERM binders, with the store outside both.  That is what makes the
-- two renaming families independent —
--
--   renᵃ  / renameᴿ  / renConv  / renAddrᴹ   move `bnd`, and extend
--       under `all` and `∀ᴿ`;
--   renᵃᵉ / renameᴿᵉ / renConvᵉ / renBseᴹ    move `bse`, and extend
--       under `Λ` and `ν`;
--
-- and neither can disturb the other, because no binder is of both
-- kinds.  Substitution mirrors this: `substAddr`/`inst₀` instantiate a
-- `∀ᴿ`'s `bnd`, `substAddrᵉ`/`instᵉ₀` instantiate a `ν`'s `bse` (to a
-- level, at `Alloc`).
--
-- WHERE THEY ARE WRITTEN.  Reduction writes an address in exactly four
-- places, and only ever the innermost base binder or a fresh level:
--
--   crossΛ   `hide 0 (bse 0)`              the color wrap
--   TyBeta   `revTy 0 (bse 0) A B`
--   TyWrap   `instReveal 0 (bse 0) A d`
--   Alloc    `M [ lvl (length Σ) ]ᵃᴹ`
--
-- `bse zero` is writable precisely BECAUSE of the split: it names the
-- newest base binder however many crossings and `∀`s stand above it.
-- With a single index counting through both halves a `Λ`'s address
-- would be `bnd (binds Ss)`, which depends on the enclosing telescope
-- and which a syntactic function on terms cannot know.
--
-- A `bnd` is never written into a term or a conversion at all.  It
-- occurs only inside representation types, under the `∀ᴿ` that binds
-- it, and as the address a `bind` entry assigns to its own name — see
-- `proof.PreserveTyWrap.∋r-nobnd` (a `bnd` has no representation) and
-- `∋a-bnd-named` (a `bnd` in scope already carries a name, so no
-- crossing can introduce an assignment to one).  It cannot be dropped,
-- though: `read-var` needs it to name a `∀`-bound variable.

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
