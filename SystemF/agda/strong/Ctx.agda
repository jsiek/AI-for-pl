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

open import Data.Nat using (ℕ; zero; suc) renaming (_<_ to _<ᵗ_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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

-- Pushing a BASE binder renumbers the base, and the stack's crossing
-- assignments may name base addresses — so the stack is carried along
-- by renaming those, which leaves its STRUCTURE, hence every pop,
-- exactly as it was.
renStk : Renameᵇ → List StackEnt → List StackEnt
renStk ρ [] = []
renStk ρ (bind ∷ Ss) = bind ∷ renStk ρ Ss
renStk ρ (asgn α ∷ Ss) = asgn (renᵃᵉ ρ α) ∷ renStk ρ Ss

⤒ : List StackEnt → List StackEnt
⤒ = renStk suc

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
    i j ℓ n : ℕ

------------------------------------------------------------------------
-- An address in scope.  NEITHER address lookup reads the stack: a `∀`
-- binds a type VARIABLE, not an address, so the only binders are the
-- base's and the store's.
------------------------------------------------------------------------

infix 4 _∣_∋a_
data _∣_∋a_ (Σ : Store) : Ctxᵗ → Addr → Set where
  a-lvl       : Σ ∋ˡ ℓ := R → Σ ∣ Γ ∋a lvl ℓ
  a-here-addr : Σ ∣ (Ss ∥ addr ∷ Bs) ∋a bse zero
  a-here-nu   : Σ ∣ (Ss ∥ nuBind R ∷ Bs) ∋a bse zero
  a-skip-addr : Σ ∣ (Ss ∥ Bs) ∋a bse j → Σ ∣ (Ss ∥ addr ∷ Bs) ∋a bse (suc j)
  a-skip-nu   : Σ ∣ (Ss ∥ Bs) ∋a bse j
              → Σ ∣ (Ss ∥ nuBind R ∷ Bs) ∋a bse (suc j)

∋a-restk : ∀ {Σ Ss Ss′ Bs α} → Σ ∣ (Ss ∥ Bs) ∋a α → Σ ∣ (Ss′ ∥ Bs) ∋a α
∋a-restk (a-lvl l) = a-lvl l
∋a-restk a-here-addr = a-here-addr
∋a-restk a-here-nu = a-here-nu
∋a-restk (a-skip-addr p) = a-skip-addr (∋a-restk p)
∋a-restk (a-skip-nu p) = a-skip-nu (∋a-restk p)

------------------------------------------------------------------------
-- A type variable ASSIGNED TO AN ADDRESS.  Only an `asgn` assigns one,
-- and passing a `bind` moves no address — so no rule needs a case
-- analysis on the address's form.  (That trichotomy was the entire
-- cost of having a `∀` bind an address.)
------------------------------------------------------------------------

infix 4 _∋n_:=_
data _∋n_:=_ : Ctxᵗ → ℕ → Addr → Set where
  n-here-asgn : (asgn α ∷ Ss ∥ Bs) ∋n zero := α
  n-skip-asgn : (Ss ∥ Bs) ∋n X := α → (asgn β ∷ Ss ∥ Bs) ∋n suc X := α
  n-skip-bind : (Ss ∥ Bs) ∋n X := α → (bind ∷ Ss ∥ Bs) ∋n suc X := α

-- A type variable BOUND BY A `∀`, and WHICH one: `X` names the `i`-th
-- `bind`, counting binds newest first.  This is what a `∀ᴿ`-bound `ᵛ
-- reads back to.
infix 4 _∋b_at_
data _∋b_at_ : List StackEnt → ℕ → ℕ → Set where
  b-here : ∀ {Ss} → (bind ∷ Ss) ∋b zero at zero
  b-asgn : ∀ {Ss α} → Ss ∋b X at i → (asgn α ∷ Ss) ∋b suc X at i
  b-bind : ∀ {Ss} → Ss ∋b X at i → (bind ∷ Ss) ∋b suc X at suc i

------------------------------------------------------------------------
-- A type variable IN SCOPE: `∋n` with the address forgotten, which is
-- all that well-formedness of a TYPE reads.
------------------------------------------------------------------------

infix 4 _∋ᵗ_
data _∋ᵗ_ : List StackEnt → ℕ → Set where
  t-here  : ∀ {e Ss} → (e ∷ Ss) ∋ᵗ zero
  t-there : ∀ {e Ss X} → Ss ∋ᵗ X → (e ∷ Ss) ∋ᵗ suc X

∋n→∋ᵗ : ∀ {Ss Bs X α} → (Ss ∥ Bs) ∋n X := α → Ss ∋ᵗ X
∋n→∋ᵗ n-here-asgn = t-here
∋n→∋ᵗ (n-skip-asgn p) = t-there (∋n→∋ᵗ p)
∋n→∋ᵗ (n-skip-bind p) = t-there (∋n→∋ᵗ p)

∋b→∋ᵗ : ∀ {Ss X i} → Ss ∋b X at i → Ss ∋ᵗ X
∋b→∋ᵗ b-here = t-here
∋b→∋ᵗ (b-asgn p) = t-there (∋b→∋ᵗ p)
∋b→∋ᵗ (b-bind p) = t-there (∋b→∋ᵗ p)

-- A variable in scope is EITHER assigned to an address OR bound by a
-- `∀`.  With a `∀` binding an address these were one judgment and the
-- address was always recoverable; now they are different things, which
-- is the point.
∋ᵗ-view : ∀ {Ss Bs X} → Ss ∋ᵗ X
  → (Σ[ α ∈ Addr ] ((Ss ∥ Bs) ∋n X := α)) ⊎ (Σ[ i ∈ ℕ ] (Ss ∋b X at i))
∋ᵗ-view {Ss = asgn α ∷ Ss} t-here = inj₁ (α , n-here-asgn)
∋ᵗ-view {Ss = bind ∷ Ss} t-here = inj₂ (zero , b-here)
∋ᵗ-view {Ss = asgn α ∷ Ss} (t-there p) with ∋ᵗ-view p
∋ᵗ-view {Ss = asgn α ∷ Ss} (t-there p) | inj₁ (β , q) = inj₁ (β , n-skip-asgn q)
∋ᵗ-view {Ss = asgn α ∷ Ss} (t-there p) | inj₂ (i , q) = inj₂ (i , b-asgn q)
∋ᵗ-view {Ss = bind ∷ Ss} (t-there p) with ∋ᵗ-view p
∋ᵗ-view {Ss = bind ∷ Ss} (t-there p) | inj₁ (β , q) = inj₁ (β , n-skip-bind q)
∋ᵗ-view {Ss = bind ∷ Ss} (t-there p) | inj₂ (i , q) = inj₂ (suc i , b-bind q)

------------------------------------------------------------------------
-- A represented address: the base's `nuBind`s and the store.
------------------------------------------------------------------------

infix 4 _∣_∋r_:=_
data _∣_∋r_:=_ (Σ : Store) : Ctxᵗ → Addr → RepTy → Set where
  r-lvl       : Σ ∋ˡ ℓ := R → Σ ∣ Γ ∋r lvl ℓ := R
  -- a `nuBind`'s representation lives OUTSIDE its own binder, so it
  -- shifts when read inside
  r-here      : Σ ∣ (Ss ∥ nuBind R ∷ Bs) ∋r bse zero := ⇑ᴿᵉ R
  r-skip-addr : Σ ∣ (Ss ∥ Bs) ∋r bse j := R
              → Σ ∣ (Ss ∥ addr ∷ Bs) ∋r bse (suc j) := ⇑ᴿᵉ R
  r-skip-nu   : Σ ∣ (Ss ∥ Bs) ∋r bse j := R
              → Σ ∣ (Ss ∥ nuBind T ∷ Bs) ∋r bse (suc j) := ⇑ᴿᵉ R

∋r-restk : ∀ {Σ Ss Ss′ Bs α R} → Σ ∣ (Ss ∥ Bs) ∋r α := R
  → Σ ∣ (Ss′ ∥ Bs) ∋r α := R
∋r-restk (r-lvl l) = r-lvl l
∋r-restk r-here = r-here
∋r-restk (r-skip-addr p) = r-skip-addr (∋r-restk p)
∋r-restk (r-skip-nu p) = r-skip-nu (∋r-restk p)

∋r→∋a : ∀ {Σ Γ α R} → Σ ∣ Γ ∋r α := R → Σ ∣ Γ ∋a α
∋r→∋a (r-lvl l) = a-lvl l
∋r→∋a r-here = a-here-nu
∋r→∋a (r-skip-addr p) = a-skip-addr (∋r→∋a p)
∋r→∋a (r-skip-nu p) = a-skip-nu (∋r→∋a p)

------------------------------------------------------------------------
-- The pop judgment: X:=α is the newest crossing assignment.  A pure
-- STACK operation, and now with no address arithmetic either.
------------------------------------------------------------------------

infix 4 _▷_:=_⇒_
data _▷_:=_⇒_ : Ctxᵗ → ℕ → Addr → Ctxᵗ → Set where
  pop-here : (asgn α ∷ Ss ∥ Bs) ▷ zero := α ⇒ (Ss ∥ Bs)
  pop-bind : (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
           → (bind ∷ Ss ∥ Bs) ▷ suc X := α ⇒ (bind ∷ Ss′ ∥ Bs)

-- Popping changes only the stack, which no address lookup reads.
∋a-pop : ∀ {Σ Ss Ss′ Bs X α β} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → Σ ∣ (Ss ∥ Bs) ∋a β → Σ ∣ (Ss′ ∥ Bs) ∋a β
∋a-pop p q = ∋a-restk q

∋a-push : ∀ {Σ Ss Ss′ Bs X α β} → (Ss ∥ Bs) ▷ X := α ⇒ (Ss′ ∥ Bs)
  → Σ ∣ (Ss′ ∥ Bs) ∋a β → Σ ∣ (Ss ∥ Bs) ∋a β
∋a-push p q = ∋a-restk q

-- An address with no name assigned to it: the notes' `Γ ∌ _:=α`.
NotAssigned : Ctxᵗ → Addr → Set
NotAssigned Γ α = ∀ {X} → Γ ∋n X := α → ⊥

-- A context assigns at most one name per address.
NameFn : Ctxᵗ → Set
NameFn Γ = ∀ {X Y α} → Γ ∋n X := α → Γ ∋n Y := α → X ≡ Y

------------------------------------------------------------------------
-- Well-formed types: well-formedness reads only WHICH NAMES are in
-- scope, never the addresses they denote.
------------------------------------------------------------------------

infix 4 _⊢ᵗ_
data _⊢ᵗ_ : Ctxᵗ → Ty → Set where
  wf-var : stk Γ ∋ᵗ X → Γ ⊢ᵗ ` X
  wf-ℕ   : Γ ⊢ᵗ `ℕ
  wf-𝔹   : Γ ⊢ᵗ `𝔹
  wf-⇒   : Γ ⊢ᵗ A → Γ ⊢ᵗ B → Γ ⊢ᵗ A ⇒ B
  wf-∀   : ∀ {Ss Bs} → (bind ∷ Ss ∥ Bs) ⊢ᵗ A → (Ss ∥ Bs) ⊢ᵗ `∀ A

∋n-rebase : ∀ {Ss Bs Bs′ X α} → (Ss ∥ Bs) ∋n X := α → (Ss ∥ Bs′) ∋n X := α
∋n-rebase n-here-asgn = n-here-asgn
∋n-rebase (n-skip-asgn p) = n-skip-asgn (∋n-rebase p)
∋n-rebase (n-skip-bind p) = n-skip-bind (∋n-rebase p)

wf-rebase : ∀ {Ss Bs Bs′ A} → (Ss ∥ Bs) ⊢ᵗ A → (Ss ∥ Bs′) ⊢ᵗ A
wf-rebase (wf-var n) = wf-var n
wf-rebase wf-ℕ = wf-ℕ
wf-rebase wf-𝔹 = wf-𝔹
wf-rebase (wf-⇒ a b) = wf-⇒ (wf-rebase a) (wf-rebase b)
wf-rebase (wf-∀ a) = wf-∀ (wf-rebase a)


------------------------------------------------------------------------
-- Well-formed representation types.  `∀ᴿ` binds a type VARIABLE, so
-- this judgment tracks how many are in scope and `ᵛ is checked against
-- that count — no context entry, and nothing to rename.
------------------------------------------------------------------------

infix 4 _∣_⊢ᴿ[_]_
data _∣_⊢ᴿ[_]_ (Σ : Store) : Ctxᵗ → ℕ → RepTy → Set where
  wfᴿ-var : Σ ∣ Γ ∋a α → Σ ∣ Γ ⊢ᴿ[ n ] `ᵃ α
  wfᴿ-bv  : i <ᵗ n → Σ ∣ Γ ⊢ᴿ[ n ] `ᵛ i
  wfᴿ-ℕ   : Σ ∣ Γ ⊢ᴿ[ n ] `ℕᴿ
  wfᴿ-𝔹   : Σ ∣ Γ ⊢ᴿ[ n ] `𝔹ᴿ
  wfᴿ-⇒   : Σ ∣ Γ ⊢ᴿ[ n ] R → Σ ∣ Γ ⊢ᴿ[ n ] T → Σ ∣ Γ ⊢ᴿ[ n ] R ⇒ᴿ T
  wfᴿ-∀   : Σ ∣ Γ ⊢ᴿ[ suc n ] R → Σ ∣ Γ ⊢ᴿ[ n ] `∀ᴿ R

-- the common case: no free `ᵛ
infix 4 _∣_⊢ᴿ_
_∣_⊢ᴿ_ : Store → Ctxᵗ → RepTy → Set
Σ ∣ Γ ⊢ᴿ R = Σ ∣ Γ ⊢ᴿ[ zero ] R

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
  -- a `∀ᴿ`-bound variable reads back to the name of the `bind` it
  -- corresponds to — no address is consulted
  read-bv  : stk Γ ∋b X at i → Σ ∣ Γ ⊢ `ᵛ i ⇓ ` X
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
  quote-bv  : stk Γ ∋b X at i → Σ ∣ Γ ⊢⌊ ` X ⌋ `ᵛ i
  quote-ℕ   : Σ ∣ Γ ⊢⌊ `ℕ ⌋ `ℕᴿ
  quote-𝔹   : Σ ∣ Γ ⊢⌊ `𝔹 ⌋ `𝔹ᴿ
  quote-⇒   : Σ ∣ Γ ⊢⌊ A ⌋ R → Σ ∣ Γ ⊢⌊ B ⌋ T
            → Σ ∣ Γ ⊢⌊ A ⇒ B ⌋ R ⇒ᴿ T
  quote-∀   : ∀ {Ss Bs} → Σ ∣ (bind ∷ Ss ∥ Bs) ⊢⌊ A ⌋ R
            → Σ ∣ (Ss ∥ Bs) ⊢⌊ `∀ A ⌋ `∀ᴿ R

-- Context well-formedness (`ok`), with its one-live-assignment-per-
-- address condition, lands with the term layer; the conversion rules
-- below need only the lookups and the pop judgment.
