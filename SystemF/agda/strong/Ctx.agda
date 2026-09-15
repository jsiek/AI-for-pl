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
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)
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

-- A context is a STACK of name entries over a BASE of address-only
-- entries.  The ordering that used to be an invariant — every name
-- entry above every address-only entry — is now the type, and that is
-- what makes address weakening cheap: it extends the BASE, leaving the
-- stack, hence every name lookup and every pop, untouched.

data BaseEnt : Set where
  addr   : BaseEnt          -- α      abstract address binder (a Λ's)
  nuBind : RepTy → BaseEnt  -- α:=R   ν-bound, not yet discharged

data StackEnt : Set where
  bind : StackEnt           -- X:α    binder assignment (a ∀'s): binds a
                            --        name AND an address
  asgn : Addr → StackEnt    -- X:=α   crossing assignment: a name for an
                            --        address bound elsewhere

infix 4 _∥_
record Ctxᵗ : Set where
  constructor _∥_
  field
    stk : List StackEnt   -- newest first
    bas : List BaseEnt    -- newest first
open Ctxᵗ

-- How many ADDRESS BINDERS the stack itself contributes.  Only a `bind`
-- (a ∀-element's binder assignment) binds an address; an `asgn` names
-- one already bound.  So the newest base entry's de Bruijn address
-- index, seen from inside a stack `Ss`, is `binds Ss`.
binds : List StackEnt → ℕ
binds [] = zero
binds (bind ∷ Ss) = suc (binds Ss)
binds (asgn α ∷ Ss) = binds Ss

private
  variable
    Σ : Store
    Γ Γ′ : Ctxᵗ
    Ss Ss′ : List StackEnt
    Bs : List BaseEnt
    A B : Ty
    R T : RepTy
    α β : Addr
    X : ℕ
    i j ℓ : ℕ

------------------------------------------------------------------------
-- An address in scope: the stack's `bind`s are address binders too, so
-- the count runs through the stack and then into the base
------------------------------------------------------------------------

-- The two bound forms are read off the two halves INDEPENDENTLY: a
-- `bnd` walks the stack and never reaches the base, a `bse` walks the
-- base and never reaches the stack.
infix 4 _∣_∋a_
data _∣_∋a_ (Σ : Store) : Ctxᵗ → Addr → Set where
  a-lvl       : Σ ∋ˡ ℓ := R → Σ ∣ Γ ∋a lvl ℓ
  a-here-bind : Σ ∣ (bind ∷ Ss ∥ Bs) ∋a bnd zero
  a-skip-bind : Σ ∣ (Ss ∥ Bs) ∋a bnd i → Σ ∣ (bind ∷ Ss ∥ Bs) ∋a bnd (suc i)
  a-skip-asgn : Σ ∣ (Ss ∥ Bs) ∋a bnd i → Σ ∣ (asgn β ∷ Ss ∥ Bs) ∋a bnd i
  a-here-addr : Σ ∣ (Ss ∥ addr ∷ Bs) ∋a bse zero
  a-here-nu   : Σ ∣ (Ss ∥ nuBind R ∷ Bs) ∋a bse zero
  a-skip-addr : Σ ∣ (Ss ∥ Bs) ∋a bse j → Σ ∣ (Ss ∥ addr ∷ Bs) ∋a bse (suc j)
  a-skip-nu   : Σ ∣ (Ss ∥ Bs) ∋a bse j
              → Σ ∣ (Ss ∥ nuBind R ∷ Bs) ∋a bse (suc j)

------------------------------------------------------------------------
-- A named address.  Names live ONLY in the stack, so this judgment
-- never mentions the base — five rules where there were nine.
------------------------------------------------------------------------

infix 4 _∋n_:=_
data _∋n_:=_ : Ctxᵗ → ℕ → Addr → Set where
  n-here-asgn   : (asgn α ∷ Ss ∥ Bs) ∋n zero := α
  n-here-bind   : (bind ∷ Ss ∥ Bs) ∋n zero := bnd zero
  n-skip-asgn   : (Ss ∥ Bs) ∋n X := α → (asgn β ∷ Ss ∥ Bs) ∋n suc X := α
  n-skip-bind-b : (Ss ∥ Bs) ∋n X := bnd i
                → (bind ∷ Ss ∥ Bs) ∋n suc X := bnd (suc i)
  n-skip-bind-l : (Ss ∥ Bs) ∋n X := lvl ℓ
                → (bind ∷ Ss ∥ Bs) ∋n suc X := lvl ℓ
  n-skip-bind-e : (Ss ∥ Bs) ∋n X := bse j
                → (bind ∷ Ss ∥ Bs) ∋n suc X := bse j

------------------------------------------------------------------------
-- A represented address.  Only the base's `nuBind` carries one; a
-- stored representation mentions only levels (`StoreOk`), so the store
-- case needs no shifting.
------------------------------------------------------------------------

infix 4 _∣_∋r_:=_
data _∣_∋r_:=_ (Σ : Store) : Ctxᵗ → Addr → RepTy → Set where
  r-lvl       : Σ ∋ˡ ℓ := R → Σ ∣ Γ ∋r lvl ℓ := R
  r-skip-bind : Σ ∣ (Ss ∥ Bs) ∋r bnd i := R
              → Σ ∣ (bind ∷ Ss ∥ Bs) ∋r bnd (suc i) := ⇑ᴿ R
  r-skip-asgn : Σ ∣ (Ss ∥ Bs) ∋r bnd i := R
              → Σ ∣ (asgn β ∷ Ss ∥ Bs) ∋r bnd i := R
  r-here      : Σ ∣ (Ss ∥ nuBind R ∷ Bs) ∋r bse zero := ⇑ᴿᵉ R
  r-skip-addr : Σ ∣ (Ss ∥ Bs) ∋r bse j := R
              → Σ ∣ (Ss ∥ addr ∷ Bs) ∋r bse (suc j) := ⇑ᴿᵉ R
  r-skip-nu   : Σ ∣ (Ss ∥ Bs) ∋r bse j := R
              → Σ ∣ (Ss ∥ nuBind T ∷ Bs) ∋r bse (suc j) := ⇑ᴿᵉ R

------------------------------------------------------------------------
-- The pop judgment: X:=α is the newest crossing assignment.  It is now
-- a STACK operation — the base cannot get in the way, so there is no
-- transparency question and the judgment is deterministic in both
-- directions (which is what makes the interior walk a function).
------------------------------------------------------------------------

infix 4 _▷_:=_⇒_
data _▷_:=_⇒_ : Ctxᵗ → ℕ → Addr → Ctxᵗ → Set where
  pop-here   : (asgn α ∷ Ss ∥ Bs) ▷ zero := α ⇒ (Ss ∥ Bs)
  pop-bind-b : (Ss ∥ Bs) ▷ X := bnd i ⇒ (Ss′ ∥ Bs)
             → (bind ∷ Ss ∥ Bs) ▷ suc X := bnd (suc i) ⇒ (bind ∷ Ss′ ∥ Bs)
  pop-bind-l : (Ss ∥ Bs) ▷ X := lvl ℓ ⇒ (Ss′ ∥ Bs)
             → (bind ∷ Ss ∥ Bs) ▷ suc X := lvl ℓ ⇒ (bind ∷ Ss′ ∥ Bs)
  pop-bind-e : (Ss ∥ Bs) ▷ X := bse j ⇒ (Ss′ ∥ Bs)
             → (bind ∷ Ss ∥ Bs) ▷ suc X := bse j ⇒ (bind ∷ Ss′ ∥ Bs)

-- An address with no name assigned to it: the notes' `Γ ∌ _:=α` side
-- condition, carried by the elements that INTRODUCE an assignment.
NotAssigned : Ctxᵗ → Addr → Set
NotAssigned Γ α = ∀ {X} → Γ ∋n X := α → ⊥

-- A context assigns at most one name per address.
NameFn : Ctxᵗ → Set
NameFn Γ = ∀ {X Y α} → Γ ∋n X := α → Γ ∋n Y := α → X ≡ Y

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
  wf-∀   : ∀ {Ss Bs} → (bind ∷ Ss ∥ Bs) ⊢ᵗ A → (Ss ∥ Bs) ⊢ᵗ `∀ A

-- THE PAYOFF OF THE SPLIT.  Names live only in the stack, so neither
-- a name lookup nor the well-formedness of a type can see the base:
-- changing the base — which is all that address weakening does — is
-- invisible to both.
∋n-rebase : ∀ {Ss Bs Bs′ X α} → (Ss ∥ Bs) ∋n X := α → (Ss ∥ Bs′) ∋n X := α
∋n-rebase n-here-asgn = n-here-asgn
∋n-rebase n-here-bind = n-here-bind
∋n-rebase (n-skip-asgn p) = n-skip-asgn (∋n-rebase p)
∋n-rebase (n-skip-bind-b p) = n-skip-bind-b (∋n-rebase p)
∋n-rebase (n-skip-bind-l p) = n-skip-bind-l (∋n-rebase p)
∋n-rebase (n-skip-bind-e p) = n-skip-bind-e (∋n-rebase p)

wf-rebase : ∀ {Ss Bs Bs′ A} → (Ss ∥ Bs) ⊢ᵗ A → (Ss ∥ Bs′) ⊢ᵗ A
wf-rebase (wf-var n) = wf-var (∋n-rebase n)
wf-rebase wf-ℕ = wf-ℕ
wf-rebase wf-𝔹 = wf-𝔹
wf-rebase (wf-⇒ a b) = wf-⇒ (wf-rebase a) (wf-rebase b)
wf-rebase (wf-∀ a) = wf-∀ (wf-rebase a)

------------------------------------------------------------------------
-- Well-formed representation types; ∀ᴿ pushes a bare address binder
------------------------------------------------------------------------

infix 4 _∣_⊢ᴿ_
data _∣_⊢ᴿ_ (Σ : Store) : Ctxᵗ → RepTy → Set where
  wfᴿ-var : Σ ∣ Γ ∋a α → Σ ∣ Γ ⊢ᴿ `ᵃ α
  wfᴿ-ℕ   : Σ ∣ Γ ⊢ᴿ `ℕᴿ
  wfᴿ-𝔹   : Σ ∣ Γ ⊢ᴿ `𝔹ᴿ
  wfᴿ-⇒   : Σ ∣ Γ ⊢ᴿ R → Σ ∣ Γ ⊢ᴿ T → Σ ∣ Γ ⊢ᴿ R ⇒ᴿ T
  wfᴿ-∀   : ∀ {Bs} → Σ ∣ ([] ∥ addr ∷ Bs) ⊢ᴿ R → Σ ∣ ([] ∥ Bs) ⊢ᴿ `∀ᴿ R

-- Store well-formedness: each representation is well-formed over the
-- strictly earlier prefix, so a representation mentions only OLDER
-- addresses and never a bound address variable.
StoreOk : Store → Set
StoreOk Σ = ∀ {ℓ R} → Σ ∋ˡ ℓ := R → take ℓ Σ ∣ ([] ∥ []) ⊢ᴿ R

------------------------------------------------------------------------
-- Reading a representation type through the name assignments in scope
------------------------------------------------------------------------

infix 4 _∣_⊢_⇓_
data _∣_⊢_⇓_ (Σ : Store) : Ctxᵗ → RepTy → Ty → Set where
  read-var : Γ ∋n X := α → Σ ∣ Γ ⊢ `ᵃ α ⇓ ` X
  read-ℕ   : Σ ∣ Γ ⊢ `ℕᴿ ⇓ `ℕ
  read-𝔹   : Σ ∣ Γ ⊢ `𝔹ᴿ ⇓ `𝔹
  read-⇒   : Σ ∣ Γ ⊢ R ⇓ A → Σ ∣ Γ ⊢ T ⇓ B → Σ ∣ Γ ⊢ R ⇒ᴿ T ⇓ A ⇒ B
  read-∀   : ∀ {Ss Bs} → Σ ∣ (bind ∷ Ss ∥ Bs) ⊢ R ⇓ A
           → Σ ∣ (Ss ∥ Bs) ⊢ `∀ᴿ R ⇓ `∀ A

------------------------------------------------------------------------
-- The address representation of a source type (⌊A⌋)
------------------------------------------------------------------------

infix 4 _∣_⊢⌊_⌋_
data _∣_⊢⌊_⌋_ (Σ : Store) : Ctxᵗ → Ty → RepTy → Set where
  quote-var : Γ ∋n X := α → Σ ∣ Γ ⊢⌊ ` X ⌋ `ᵃ α
  quote-ℕ   : Σ ∣ Γ ⊢⌊ `ℕ ⌋ `ℕᴿ
  quote-𝔹   : Σ ∣ Γ ⊢⌊ `𝔹 ⌋ `𝔹ᴿ
  quote-⇒   : Σ ∣ Γ ⊢⌊ A ⌋ R → Σ ∣ Γ ⊢⌊ B ⌋ T
            → Σ ∣ Γ ⊢⌊ A ⇒ B ⌋ R ⇒ᴿ T
  quote-∀   : ∀ {Ss Bs} → Σ ∣ (bind ∷ Ss ∥ Bs) ⊢⌊ A ⌋ R
            → Σ ∣ (Ss ∥ Bs) ⊢⌊ `∀ A ⌋ `∀ᴿ R

-- Context well-formedness (`ok`), with its one-live-assignment-per-
-- address condition, lands with the term layer; the conversion rules
-- below need only the lookups and the pop judgment.
