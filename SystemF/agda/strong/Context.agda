module strong.Context where

-- Strong System F — the two contexts and their lookup relations (prefix design).
--
-- TWO CONTEXTS (see notes.md).  A judgement is  Δ ∣ Γ ⊢ M : A  where
--
--   Δ : TCtx   the *type* context — a telescope of type-variable entries, each
--              abstract (from ∀/Λ) or revealed (X:=A).  There is NO conceal marker.
--   Γ : Ctx    the *term* context — a plain list of types scoped in Δ.
--
-- Concealment.  A conceal ↓[X:=A] does not extend Δ.  Its body is typed in the
-- *prefix*  Δ ↓ X  — the part of Δ deeper than X (bound before it), X's existential
-- scope.  So lookup is ordinary System F (no marker to skip), and representation
-- lookup is SHIFT-FREE: the rep stored in `rvld A` is a type over its tail, and the
-- tail is exactly the prefix, so it is returned unchanged (no ⇑ᵗ).

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types

------------------------------------------------------------------------
-- The type context
------------------------------------------------------------------------

data TyEntry : Set where
  abst : TyEntry        -- abstract type variable X       (from ∀ / Λ)
  rvld : Ty → TyEntry   -- revealed type variable X:=A    (rep A over the tail)

TCtx : Set
TCtx = List TyEntry

variable
  Δ : TCtx
  Γ : List Ty
  A B C : Ty
  X Y Z : ℕ
  x : ℕ
  E : TyEntry

------------------------------------------------------------------------
-- Context prefix   Δ ↓ X
------------------------------------------------------------------------

-- Δ ↓ X : the part of Δ deeper than X — drop X's entry and everything shallower
-- (indices ≤ X), keeping the deeper tail.  This is X's existential scope, used as
-- the context of a conceal body.  Partial in spirit (X must be in scope); the []
-- clause is a never-reached default.
infix 5 _↓_
_↓_ : TCtx → ℕ → TCtx
[]           ↓ X     = []
(abst   ∷ Δ) ↓ zero  = Δ
(rvld A ∷ Δ) ↓ zero  = Δ
(abst   ∷ Δ) ↓ suc X = Δ ↓ X
(rvld A ∷ Δ) ↓ suc X = Δ ↓ X

------------------------------------------------------------------------
-- Type-variable lookup
------------------------------------------------------------------------

-- Δ ∋tv X : the variable at index X is in scope.  Ordinary lookup — no markers.
infix 4 _∋tv_
data _∋tv_ : TCtx → ℕ → Set where
  here-abst : (abst ∷ Δ) ∋tv zero
  here-rvld : (rvld A ∷ Δ) ∋tv zero
  skip-abst : Δ ∋tv X → (abst ∷ Δ) ∋tv suc X
  skip-rvld : Δ ∋tv X → (rvld A ∷ Δ) ∋tv suc X

-- Δ ∋ X := A : the variable at index X is revealed with representation A.  The rep
-- is a type over the tail below X's entry — which is exactly the prefix Δ ↓ X — so
-- it is returned WITHOUT shifting.
infix 4 _∋_:=_
data _∋_:=_ : TCtx → ℕ → Ty → Set where
  here      : (rvld A ∷ Δ) ∋ zero := A
  skip-abst : Δ ∋ X := A → (abst ∷ Δ) ∋ suc X := A
  skip-rvld : Δ ∋ X := A → (rvld B ∷ Δ) ∋ suc X := A

------------------------------------------------------------------------
-- Well-formed types
------------------------------------------------------------------------

infix 4 _⊢_
data _⊢_ : TCtx → Ty → Set where
  wf-var : Δ ∋tv X → Δ ⊢ ` X
  wf-ℕ   : Δ ⊢ `ℕ
  wf-𝔹   : Δ ⊢ `𝔹
  wf-⇒   : Δ ⊢ A → Δ ⊢ B → Δ ⊢ (A ⇒ B)
  wf-∀   : (abst ∷ Δ) ⊢ A → Δ ⊢ (`∀ A)

------------------------------------------------------------------------
-- Well-formed type contexts
------------------------------------------------------------------------

-- Each entry is well-formed in its own prefix.
infix 4 ⊢_
data ⊢_ : TCtx → Set where
  ⊢∅    : ⊢ []
  ⊢abst : ⊢ Δ →         ⊢ (abst ∷ Δ)
  ⊢rvld : ⊢ Δ → Δ ⊢ A → ⊢ (rvld A ∷ Δ)

------------------------------------------------------------------------
-- The term context and its lookup
------------------------------------------------------------------------

Ctx : Set
Ctx = List Ty

-- Γ ∋ x ⦂ A : ordinary de Bruijn term-variable lookup.  The (conceal) rule clears
-- Γ to [], so a conceal body starts a fresh term scope.
infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → ℕ → Ty → Set where
  here  : ∀ {Γ A}     →              (A ∷ Γ) ∋ zero  ⦂ A
  there : ∀ {Γ A B x} → Γ ∋ x ⦂ A → (B ∷ Γ) ∋ suc x ⦂ A

-- ⤊ Γ : shift every type of the term context when the type context grows by one
-- variable (∀/Λ and reveal).
⤊ : Ctx → Ctx
⤊ = map ⇑ᵗ

-- Δ ⊢* Γ : the term context Γ is well-formed in the type context Δ.
infix 4 _⊢*_
data _⊢*_ : TCtx → Ctx → Set where
  ⊢[]  :                  Δ ⊢* []
  _⊢∷_ : Δ ⊢ A → Δ ⊢* Γ → Δ ⊢* (A ∷ Γ)

------------------------------------------------------------------------
-- Lookup and well-formedness
------------------------------------------------------------------------

-- ∋tv produces a well-formed type variable — this is exactly wf-var.
∋tv-⊢ : Δ ∋tv X → Δ ⊢ ` X
∋tv-⊢ = wf-var

-- a revealed variable is in scope (forget its representation)
∋:=→∋tv : Δ ∋ X := A → Δ ∋tv X
∋:=→∋tv here          = here-rvld
∋:=→∋tv (skip-abst p) = skip-abst (∋:=→∋tv p)
∋:=→∋tv (skip-rvld p) = skip-rvld (∋:=→∋tv p)

------------------------------------------------------------------------
-- Sanity checks
------------------------------------------------------------------------

private
  -- index 0 : X:=𝔹 | index 1 : Y:=ℕ   (both reps closed)
  Δ0 : TCtx
  Δ0 = rvld `𝔹 ∷ rvld `ℕ ∷ []

  -- the prefix drops X's entry and everything shallower
  _ : Δ0 ↓ 0 ≡ rvld `ℕ ∷ []
  _ = refl
  _ : Δ0 ↓ 1 ≡ []
  _ = refl

  -- index 0 : Y:=X (rep mentions the deeper X) | index 1 : X:=ℕ
  Δ1 : TCtx
  Δ1 = rvld (` 0) ∷ rvld `ℕ ∷ []

  -- Y's prefix is just X:=ℕ …
  _ : Δ1 ↓ 0 ≡ rvld `ℕ ∷ []
  _ = refl
  -- … and looking up Y is SHIFT-FREE: it returns ` 0 (the rep over that prefix),
  -- NOT ` 1.  The old marker design returned ⇑ᵗ (` 0) = ` 1.
  _ : Δ1 ∋ 0 := ` 0
  _ = here
  _ : Δ1 ∋ 1 := `ℕ
  _ = skip-rvld here

  -- the rep really is well-formed in its prefix
  _ : (Δ1 ↓ 0) ⊢ ` 0
  _ = wf-var here-rvld

  -- a term context of closed types is well-formed in any Δ
  _ : Δ0 ⊢* (`ℕ ∷ `𝔹 ∷ [])
  _ = wf-ℕ ⊢∷ (wf-𝔹 ⊢∷ ⊢[])
