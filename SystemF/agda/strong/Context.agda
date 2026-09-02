module strong.Context where

-- Strong System F — the two contexts and their lookup relations.
--
-- TWO CONTEXTS (see notes.md).  A judgement is  Δ ; Γ ⊢ M : A  where
--
--   Δ : TCtx   the *type* context — a telescope of type-variable entries, each
--              abstract (from ∀/Λ) or revealed (X:=A), together with conceal
--              markers `cncl X`.
--   Γ : Ctx    the *term* context — a plain list of types scoped in Δ.
--
-- Concealment.  The marker ↓X of the name-based notes is a SEPARATE entry
-- `cncl X` that names, by de Bruijn index, the variable it seals.  Concealing X
-- PREPENDS `cncl X`; it does NOT overwrite X's `rvld` entry.
-- Keeping the `rvld` in place is what preserves well-formedness of the context:
-- a later revealed variable whose representation mentions X (e.g. Y:=(X→X)) was
-- checked in its own prefix, where X was revealed, and that prefix is untouched.
--
-- Markers are NON-COUNTING: a type-variable index skips over a `cncl` without
-- changing, so concealing shifts no indices and the body's types are literally
-- types over Δ.  A lookup passes transparently over a marker for a *different*
-- variable and is BLOCKED by the marker for its own variable — realising ∋-mskip
-- and "no rule for ↓X ∋ X".
--
-- reveal vs conceal are asymmetric: reveal BINDS a fresh revealed variable in
-- its body (context extension `rvld A ∷ Δ`); conceal REFERS to an existing
-- revealed variable X and blocks it (`cncl X ∷ Δ`).

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import strong.Types

------------------------------------------------------------------------
-- The type context
------------------------------------------------------------------------

data TyEntry : Set where
  abst : TyEntry        -- abstract type variable X            (from ∀ / Λ)   [counting]
  rvld : Ty → TyEntry   -- revealed type variable X:=A         (rep A over the tail) [counting]
  cncl : ℕ → TyEntry    -- conceal marker sealing index X      (the ↓X marker) [NON-counting]

TCtx : Set
TCtx = List TyEntry

variable
  Δ : TCtx
  Γ : List Ty
  A B C : Ty
  X Y Z : ℕ
  n x : ℕ
  E : TyEntry

-- The two context extensions are written directly: reveal binds a fresh
-- revealed variable (rvld A ∷ Δ); conceal blocks an existing revealed variable
-- (cncl X ∷ Δ), leaving Δ and X's `rvld` entry intact.

------------------------------------------------------------------------
-- Type-variable lookup
------------------------------------------------------------------------

-- Δ ∋tv X : the variable at index X is in scope — abstract or revealed and not
-- blocked by a marker.  A counting entry (abst/rvld) is skipped with suc; a
-- marker `cncl n` is skipped WITHOUT changing the index, and only when n ≢ X.
infix 4 _∋tv_
data _∋tv_ : TCtx → ℕ → Set where
  here-abst : (abst ∷ Δ) ∋tv zero
  here-rvld : (rvld A ∷ Δ) ∋tv zero
  skip-abst : Δ ∋tv X → (abst ∷ Δ) ∋tv suc X
  skip-rvld : Δ ∋tv X → (rvld A ∷ Δ) ∋tv suc X
  skip-cncl : n ≢ X → Δ ∋tv X → (cncl n ∷ Δ) ∋tv X
  -- no clause for  (cncl X ∷ Δ) ∋tv X : the marker blocks its own variable.

-- Δ ∋ X := A : the variable at index X is revealed with representation A,
-- expressed over Δ.  A counting entry shifts the rep by ⇑ᵗ; a marker does not
-- (it introduces no type variable), and blocks its own variable.
infix 4 _∋_:=_
data _∋_:=_ : TCtx → ℕ → Ty → Set where
  here      : (rvld A ∷ Δ) ∋ zero := ⇑ᵗ A
  skip-abst : Δ ∋ X := A → (abst ∷ Δ) ∋ suc X := ⇑ᵗ A
  skip-rvld : Δ ∋ X := A → (rvld B ∷ Δ) ∋ suc X := ⇑ᵗ A
  skip-cncl : n ≢ X → Δ ∋ X := A → (cncl n ∷ Δ) ∋ X := A

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

-- Each entry is well-formed in its own prefix.  A marker `cncl X` requires only
-- that X is in scope in the (untouched) tail — so concealment preserves ⊢:
--   ⊢ Δ  and  Δ ∋tv X   give   ⊢ (conceal X Δ).
infix 4 ⊢_
data ⊢_ : TCtx → Set where
  ⊢∅    : ⊢ []
  ⊢abst : ⊢ Δ →           ⊢ (abst ∷ Δ)
  ⊢rvld : ⊢ Δ → Δ ⊢ A →   ⊢ (rvld A ∷ Δ)
  ⊢cncl : ⊢ Δ → Δ ∋tv X → ⊢ (cncl X ∷ Δ)

------------------------------------------------------------------------
-- The term context and its lookup
------------------------------------------------------------------------

Ctx : Set
Ctx = List Ty

-- Γ ∋ x ⦂ A : ordinary de Bruijn term-variable lookup.  No marker interaction:
-- the (conceal) rule clears Γ to [], so a conceal body starts a fresh term
-- scope and can never reach an outer term variable.
infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → ℕ → Ty → Set where
  here  : ∀ {Γ A}     →              (A ∷ Γ) ∋ zero  ⦂ A
  there : ∀ {Γ A B x} → Γ ∋ x ⦂ A → (B ∷ Γ) ∋ suc x ⦂ A

-- ⤊ Γ : shift every type of the term context when the type context grows by one
-- *counting* variable (∀/Λ and reveal).  (Concealment does not grow it.)
⤊ : Ctx → Ctx
⤊ = map ⇑ᵗ

-- Δ ⊢* Γ : the term context Γ is well-formed in the type context Δ — every one
-- of its types is well-formed in Δ.  All entries are scoped in the *current* Δ,
-- so growing Δ with a counting variable (∀/Λ, reveal) requires ⤊ Γ to restore
-- this.  The full context (Δ ; Γ) is well-formed when  ⊢ Δ  and  Δ ⊢* Γ.
infix 4 _⊢*_
data _⊢*_ : TCtx → Ctx → Set where
  ⊢[]  :                    Δ ⊢* []
  _⊢∷_ : Δ ⊢ A → Δ ⊢* Γ → Δ ⊢* (A ∷ Γ)

------------------------------------------------------------------------
-- Lookup and well-formedness
------------------------------------------------------------------------

-- ∋tv produces a well-formed type variable — this is exactly wf-var.
∋tv-⊢ : Δ ∋tv X → Δ ⊢ ` X
∋tv-⊢ = wf-var

-- The analogous statement for ∋ := (a looked-up representation is well-formed in
-- the current context) is FALSE: a marker can conceal a variable the
-- representation mentions.  See the counterexample in the sanity checks below.

------------------------------------------------------------------------
-- Sanity checks
------------------------------------------------------------------------

private
  -- index 0 : 𝔹 revealed | index 1 : ℕ revealed
  Δ0 : TCtx
  Δ0 = rvld `𝔹 ∷ rvld `ℕ ∷ []

  -- after concealing index 1, index 0 is still in scope but index 1 is blocked
  _ : (cncl 1 ∷ Δ0) ∋tv 0
  _ = skip-cncl (λ ()) here-rvld

  _ : ¬ ((cncl 1 ∷ Δ0) ∋tv 1)
  _ = λ { (skip-cncl 1≢1 _) → 1≢1 refl }

  -- the failure case that motivated the redesign: Y:=(X→X) revealed over X:=ℕ.
  --   index 0 : Y with representation (`0 ⇒ `0) mentioning X   | index 1 : X = ℕ
  Δ1 : TCtx
  Δ1 = rvld (` 0 ⇒ ` 0) ∷ rvld `ℕ ∷ []

  _ : ⊢ Δ1
  _ = ⊢rvld (⊢rvld ⊢∅ wf-ℕ) (wf-⇒ (wf-var here-rvld) (wf-var here-rvld))

  -- concealing X (index 1) KEEPS the context well-formed: Δ1 is untouched, so
  -- Y's representation (which mentions X) is still fine.
  _ : ⊢ (cncl 1 ∷ Δ1)
  _ = ⊢cncl (⊢rvld (⊢rvld ⊢∅ wf-ℕ) (wf-⇒ (wf-var here-rvld) (wf-var here-rvld)))
            (skip-rvld here-rvld)

  -- …but looking up Y (index 0) past the marker returns its representation
  -- (`1 ⇒ `1), which mentions the CONCEALED X (index 1) — and that is NOT
  -- well-formed here.  So ∋ := does not produce a well-formed type.
  _ : (cncl 1 ∷ Δ1) ∋ 0 := (` 1 ⇒ ` 1)
  _ = skip-cncl (λ ()) here

  _ : ¬ ((cncl 1 ∷ Δ1) ⊢ (` 1 ⇒ ` 1))
  _ = λ { (wf-⇒ (wf-var (skip-cncl 1≢1 _)) _) → 1≢1 refl }

  -- a term context of closed types is well-formed in any Δ
  _ : Δ0 ⊢* (`ℕ ∷ `𝔹 ∷ [])
  _ = wf-ℕ ⊢∷ (wf-𝔹 ⊢∷ ⊢[])
