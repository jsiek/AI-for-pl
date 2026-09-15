module strong.Ctx where

-- Strong System F v8 — the global store, contexts, and their lookups.
--
-- The store Σ is append-only, oldest first: a level is a position from
-- the start, so `Alloc`'s snoc extends the store without disturbing any
-- existing level.  A context Γ holds the LOCAL structure, with name
-- entries in TWO FORMS:
--
--   bind     X:α    a BINDER assignment, pushed by the `∀` conversion
--                   element and the type-level `∀` rules; it binds an
--                   address and a name together, and is TRANSPARENT to
--                   the stack.
--   asgn α   X:=α   a CROSSING assignment, pushed by `Λ` and pushed or
--                   popped by the atomic conversion elements; these
--                   form the STACK.
--
-- plus bare address binders (`addr`, a Λ's α or a `∀ᴿ` descent) and
-- ν-bound represented addresses (`nuBind R`, not yet discharged).
--
-- De Bruijn accounting: a type-variable name X counts the name entries
-- (`bind` and `asgn`); a bound address `bnd i` counts the address
-- binders (`addr`, `nuBind`, `bind`).  The pop judgment `Γ ▷ X := α ⇒
-- Γ′` says X:=α is the NEWEST crossing assignment in Γ and Γ′ removes
-- it: v7's rightmost-visible judgment, with binder assignments now
-- transparent alongside address entries.  There is no rule through a
-- crossing assignment — "every conceal removes the latest visible
-- source name".

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _∷ʳ_; take)
open import strong.Types using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀)
open import strong.RepresentationTypes

------------------------------------------------------------------------
-- The global store
------------------------------------------------------------------------

Store : Set
Store = List RepTy

infix 4 _∋ˡ_:=_
data _∋ˡ_:=_ : Store → ℕ → RepTy → Set where
  l-here  : ∀ {Σ R} → (R ∷ Σ) ∋ˡ zero := R
  l-there : ∀ {Σ S ℓ R} → Σ ∋ˡ ℓ := R → (S ∷ Σ) ∋ˡ suc ℓ := R

------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

data Ent : Set where
  addr   : Ent            -- α       abstract address binder
  nuBind : RepTy → Ent    -- α:=R    ν-bound address, not yet discharged
  bind   : Ent            -- X:α     binder assignment (transparent)
  asgn   : Addr → Ent     -- X:=α    crossing assignment (the stack)

Ctxᵗ : Set
Ctxᵗ = List Ent

private
  variable
    Σ : Store
    Γ Γ′ : Ctxᵗ
    A B : Ty
    R S : RepTy
    α β : Addr
    X : ℕ
    i ℓ : ℕ

------------------------------------------------------------------------
-- An address in scope
------------------------------------------------------------------------

infix 4 _∣_∋a_
data _∣_∋a_ (Σ : Store) : Ctxᵗ → Addr → Set where
  a-lvl       : Σ ∋ˡ ℓ := R → Σ ∣ Γ ∋a lvl ℓ
  a-here-addr : Σ ∣ (addr ∷ Γ) ∋a bnd zero
  a-here-nu   : Σ ∣ (nuBind R ∷ Γ) ∋a bnd zero
  a-here-bind : Σ ∣ (bind ∷ Γ) ∋a bnd zero
  a-skip-addr : Σ ∣ Γ ∋a bnd i → Σ ∣ (addr ∷ Γ) ∋a bnd (suc i)
  a-skip-nu   : Σ ∣ Γ ∋a bnd i → Σ ∣ (nuBind R ∷ Γ) ∋a bnd (suc i)
  a-skip-bind : Σ ∣ Γ ∋a bnd i → Σ ∣ (bind ∷ Γ) ∋a bnd (suc i)
  a-skip-asgn : Σ ∣ Γ ∋a bnd i → Σ ∣ (asgn β ∷ Γ) ∋a bnd i

------------------------------------------------------------------------
-- A named address: X is the de Bruijn count of name entries, and the
-- address shifts through the address binders above it
------------------------------------------------------------------------

infix 4 _∋n_:=_
data _∋n_:=_ : Ctxᵗ → ℕ → Addr → Set where
  n-here-asgn   : (asgn α ∷ Γ) ∋n zero := α
  n-here-bind   : (bind ∷ Γ) ∋n zero := bnd zero
  n-skip-asgn   : Γ ∋n X := α → (asgn β ∷ Γ) ∋n suc X := α
  n-skip-bind-b : Γ ∋n X := bnd i → (bind ∷ Γ) ∋n suc X := bnd (suc i)
  n-skip-bind-l : Γ ∋n X := lvl ℓ → (bind ∷ Γ) ∋n suc X := lvl ℓ
  n-skip-addr-b : Γ ∋n X := bnd i → (addr ∷ Γ) ∋n X := bnd (suc i)
  n-skip-addr-l : Γ ∋n X := lvl ℓ → (addr ∷ Γ) ∋n X := lvl ℓ
  n-skip-nu-b   : Γ ∋n X := bnd i → (nuBind R ∷ Γ) ∋n X := bnd (suc i)
  n-skip-nu-l   : Γ ∋n X := lvl ℓ → (nuBind R ∷ Γ) ∋n X := lvl ℓ

------------------------------------------------------------------------
-- A represented address.  A stored representation mentions only levels
-- (`StoreOk` below), so the store case needs no shifting; a ν-bound
-- representation is shifted into the whole context, as its bound
-- addresses cross the binders above it.
------------------------------------------------------------------------

infix 4 _∣_∋r_:=_
data _∣_∋r_:=_ (Σ : Store) : Ctxᵗ → Addr → RepTy → Set where
  r-lvl       : Σ ∋ˡ ℓ := R → Σ ∣ Γ ∋r lvl ℓ := R
  r-here      : Σ ∣ (nuBind R ∷ Γ) ∋r bnd zero := ⇑ᴿ R
  r-skip-addr : Σ ∣ Γ ∋r bnd i := R → Σ ∣ (addr ∷ Γ) ∋r bnd (suc i) := ⇑ᴿ R
  r-skip-nu   : Σ ∣ Γ ∋r bnd i := R → Σ ∣ (nuBind S ∷ Γ) ∋r bnd (suc i) := ⇑ᴿ R
  r-skip-bind : Σ ∣ Γ ∋r bnd i := R → Σ ∣ (bind ∷ Γ) ∋r bnd (suc i) := ⇑ᴿ R
  r-skip-asgn : Σ ∣ Γ ∋r bnd i := R → Σ ∣ (asgn β ∷ Γ) ∋r bnd i := R

------------------------------------------------------------------------
-- The pop judgment: X:=α is the newest crossing assignment; Γ′ removes
-- it.  No rule through a crossing assignment.
------------------------------------------------------------------------

infix 4 _▷_:=_⇒_
data _▷_:=_⇒_ : Ctxᵗ → ℕ → Addr → Ctxᵗ → Set where
  pop-here   : (asgn α ∷ Γ) ▷ zero := α ⇒ Γ
  pop-bind-b : Γ ▷ X := bnd i ⇒ Γ′
             → (bind ∷ Γ) ▷ suc X := bnd (suc i) ⇒ (bind ∷ Γ′)
  pop-bind-l : Γ ▷ X := lvl ℓ ⇒ Γ′
             → (bind ∷ Γ) ▷ suc X := lvl ℓ ⇒ (bind ∷ Γ′)
-- Only BINDER ASSIGNMENTS are transparent.  Address entries need not
-- be: a crossing assignment is always pushed above the address binders
-- in scope when it is created (a `Λ` pushes `asgn` above its own
-- `addr`; a `ν`'s entry is introduced at a boundary's EXTERIOR, with
-- the conversion's crossings inside it), so no derivation needs to pop
-- one from underneath.  Dropping those rules makes the judgment
-- DETERMINISTIC in both directions, which is what makes the interior
-- walk a function (see proof.Interior).

------------------------------------------------------------------------
-- Well-formed types: every variable names an address (either entry
-- form); ∀ pushes a binder assignment
------------------------------------------------------------------------

infix 4 _⊢ᵗ_
data _⊢ᵗ_ : Ctxᵗ → Ty → Set where
  wf-var : Γ ∋n X := α → Γ ⊢ᵗ ` X
  wf-ℕ   : Γ ⊢ᵗ `ℕ
  wf-𝔹   : Γ ⊢ᵗ `𝔹
  wf-⇒   : Γ ⊢ᵗ A → Γ ⊢ᵗ B → Γ ⊢ᵗ A ⇒ B
  wf-∀   : (bind ∷ Γ) ⊢ᵗ A → Γ ⊢ᵗ `∀ A

------------------------------------------------------------------------
-- Well-formed representation types; ∀ᴿ pushes a bare address binder
------------------------------------------------------------------------

infix 4 _∣_⊢ᴿ_
data _∣_⊢ᴿ_ (Σ : Store) : Ctxᵗ → RepTy → Set where
  wfᴿ-var : Σ ∣ Γ ∋a α → Σ ∣ Γ ⊢ᴿ `ᵃ α
  wfᴿ-ℕ   : Σ ∣ Γ ⊢ᴿ `ℕᴿ
  wfᴿ-𝔹   : Σ ∣ Γ ⊢ᴿ `𝔹ᴿ
  wfᴿ-⇒   : Σ ∣ Γ ⊢ᴿ R → Σ ∣ Γ ⊢ᴿ S → Σ ∣ Γ ⊢ᴿ R ⇒ᴿ S
  wfᴿ-∀   : Σ ∣ (addr ∷ Γ) ⊢ᴿ R → Σ ∣ Γ ⊢ᴿ `∀ᴿ R

-- Store well-formedness: each representation is well-formed over the
-- strictly earlier prefix, so a representation mentions only OLDER
-- addresses and never a bound address variable.
StoreOk : Store → Set
StoreOk Σ = ∀ {ℓ R} → Σ ∋ˡ ℓ := R → take ℓ Σ ∣ [] ⊢ᴿ R

------------------------------------------------------------------------
-- Reading a representation type through the name assignments in scope
------------------------------------------------------------------------

infix 4 _∣_⊢_⇓_
data _∣_⊢_⇓_ (Σ : Store) : Ctxᵗ → RepTy → Ty → Set where
  read-var : Γ ∋n X := α → Σ ∣ Γ ⊢ `ᵃ α ⇓ ` X
  read-ℕ   : Σ ∣ Γ ⊢ `ℕᴿ ⇓ `ℕ
  read-𝔹   : Σ ∣ Γ ⊢ `𝔹ᴿ ⇓ `𝔹
  read-⇒   : Σ ∣ Γ ⊢ R ⇓ A → Σ ∣ Γ ⊢ S ⇓ B → Σ ∣ Γ ⊢ R ⇒ᴿ S ⇓ A ⇒ B
  read-∀   : Σ ∣ (bind ∷ Γ) ⊢ R ⇓ A → Σ ∣ Γ ⊢ `∀ᴿ R ⇓ `∀ A

------------------------------------------------------------------------
-- The address representation of a source type (⌊A⌋)
------------------------------------------------------------------------

infix 4 _∣_⊢⌊_⌋_
data _∣_⊢⌊_⌋_ (Σ : Store) : Ctxᵗ → Ty → RepTy → Set where
  quote-var : Γ ∋n X := α → Σ ∣ Γ ⊢⌊ ` X ⌋ `ᵃ α
  quote-ℕ   : Σ ∣ Γ ⊢⌊ `ℕ ⌋ `ℕᴿ
  quote-𝔹   : Σ ∣ Γ ⊢⌊ `𝔹 ⌋ `𝔹ᴿ
  quote-⇒   : Σ ∣ Γ ⊢⌊ A ⌋ R → Σ ∣ Γ ⊢⌊ B ⌋ S
            → Σ ∣ Γ ⊢⌊ A ⇒ B ⌋ R ⇒ᴿ S
  quote-∀   : Σ ∣ (bind ∷ Γ) ⊢⌊ A ⌋ R → Σ ∣ Γ ⊢⌊ `∀ A ⌋ `∀ᴿ R

-- Context well-formedness (`ok`), with its one-live-assignment-per-
-- address condition, lands with the term layer; the conversion rules
-- below need only the lookups and the pop judgment.
