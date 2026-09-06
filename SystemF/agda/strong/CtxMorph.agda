module strong.CtxMorph where

-- Strong System F — the BOUNDARY'S CONTEXT MORPHISM and its well-formedness.
--
-- A boundary is  M ⟪ Θ , c ⟫  (strong.Terms) with ONE frame change:
--
--   Θ : CtxMorph   the context morphism, rep-free except for binders
--        bind A   BINDS a fresh interior slot; A is its representation, read
--                on `unlockedScope Θ′ Δ` (the tail's unmasks applied, its
--                locks lifted — where the conversion is read).  The only
--                rep-carrying form; born once, bound once.
--        lock X   MASKS exterior slot X: the interior may not NAME it.  The
--                entry is RETAINED on the type context — nothing is dropped
--                and nothing is re-spelled, so there is no demotion.
--        unlock X UNMASKS exterior slot X; it claims nothing but that X IS
--                masked where it acts (no vacuous unlocks).
--
-- This module defines the morphism, the type contexts it induces
-- (`scope`, `unlockedScope`, `interior`, `convCtx`), their refinement
-- transports, and the well-formedness judgement `Δ ⊢ᵐ Θ`.  Terms and
-- typing are in strong.Terms, which re-exports this module.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.Ctx

private
  variable
    Δ Δ′ : Ctxᵗ
    A B : Ty
    X Y : ℕ

------------------------------------------------------------------------
-- 1.  The boundary context morphism
------------------------------------------------------------------------

data MorphEnt : Set where
  bind : Ty → MorphEnt      -- BINDS a fresh slot at rep A (A over the exterior)
  unlock : ℕ → MorphEnt       -- unmask exterior slot X   (name only)
  lock : ℕ → MorphEnt       -- mask   exterior slot X   (name only)

CtxMorph : Set
CtxMorph = List MorphEnt

repsOf : CtxMorph → List Ty
repsOf []             = []
repsOf (bind A ∷ Θ)   = A ∷ repsOf Θ
repsOf (unlock X ∷ Θ) = repsOf Θ
repsOf (lock X ∷ Θ)   = repsOf Θ

-- `numBinds` is the boundary's FRAME EXTENSION: the number of binders it
-- adds.  It is the only surviving list arithmetic; cmax/dropN have no
-- analogue, because conceal masks in place.
numBinds : CtxMorph → ℕ
numBinds Θ = length (repsOf Θ)

-- The masks (`lock`) and unmasks (`unlock`), applied in place.
scope : CtxMorph → Ctxᵗ → Ctxᵗ
scope []             Δ = Δ
scope (bind A ∷ Θ)   Δ = scope Θ Δ
scope (unlock X ∷ Θ) Δ = unmask X (scope Θ Δ)
scope (lock X ∷ Θ)   Δ = mask X (scope Θ Δ)

-- The CONVERSION CONTEXT's slots: like `scope` but WITHOUT the conceal
-- masks, so a `seal X` can resolve X at its binder.  This is
-- binder-syntactic lookup: the licence is read on the type context that
-- encloses the boundary, never inside it.
unlockedScope : CtxMorph → Ctxᵗ → Ctxᵗ
unlockedScope []             Δ = Δ
unlockedScope (bind A ∷ Θ)   Δ = unlockedScope Θ Δ
unlockedScope (unlock X ∷ Θ) Δ = unmask X (unlockedScope Θ Δ)
unlockedScope (lock X ∷ Θ)   Δ = unlockedScope Θ Δ

-- What replaces `intOf`: the same slot list, the interior mask, and the
-- binder extension.  Nothing is dropped and no rep is recomputed.
interior : CtxMorph → Ctxᵗ → Ctxᵗ
interior Θ Δ = pushBinds (repsOf Θ) (scope Θ Δ)

convCtx : CtxMorph → Ctxᵗ → Ctxᵗ
convCtx Θ Δ = pushBinds (repsOf Θ) (unlockedScope Θ Δ)

-- The interior type context is the conversion context with Θ's bind
-- masks on, so anything well formed inside is well formed on the
-- conversion context.
scope⊑unlockedScope : (Θ : CtxMorph) (Δ : Ctxᵗ)
  → scope Θ Δ ⊑ unlockedScope Θ Δ
scope⊑unlockedScope []             Δ = ⊑-refl Δ
scope⊑unlockedScope (bind A ∷ Θ)   Δ = scope⊑unlockedScope Θ Δ
scope⊑unlockedScope (unlock X ∷ Θ) Δ =
  ⊑-updateAt unmaskEnt unmaskEnt-comm unmaskEnt-mono
    (scope⊑unlockedScope Θ Δ)
scope⊑unlockedScope (lock X ∷ Θ)   Δ = mask-⊑ X (scope⊑unlockedScope Θ Δ)

interior⊑convCtx : (Θ : CtxMorph) (Δ : Ctxᵗ) → interior Θ Δ ⊑ convCtx Θ Δ
interior⊑convCtx Θ Δ = ⊑-pushBinds (repsOf Θ) (scope⊑unlockedScope Θ Δ)

-- The CONVERSION CONTEXT only ever ADDS nameability to the plain
-- exterior: `unlockedScope` skips the binds and the locks, and an
-- `unlock` merely restores.  (`scope` would not do — masking is what a
-- lock is for.)
Δ⊑unlockedScope : (Θ : CtxMorph) (Δ : Ctxᵗ) → Δ ⊑ unlockedScope Θ Δ
Δ⊑unlockedScope []             Δ = ⊑-refl Δ
Δ⊑unlockedScope (bind A ∷ Θ)   Δ = Δ⊑unlockedScope Θ Δ
Δ⊑unlockedScope (unlock X ∷ Θ) Δ =
  ⊑-trans (Δ⊑unlockedScope Θ Δ) (unmask-⊑ X (unlockedScope Θ Δ))
Δ⊑unlockedScope (lock X ∷ Θ)   Δ = Δ⊑unlockedScope Θ Δ

⊑-scope : (Θ : CtxMorph) → Δ ⊑ Δ′ → scope Θ Δ ⊑ scope Θ Δ′
⊑-scope []             ls = ls
⊑-scope (bind A ∷ Θ)   ls = ⊑-scope Θ ls
⊑-scope (unlock X ∷ Θ) ls =
  ⊑-updateAt unmaskEnt unmaskEnt-comm unmaskEnt-mono (⊑-scope Θ ls)
⊑-scope (lock X ∷ Θ)   ls =
  ⊑-updateAt masked masked-comm masked-mono (⊑-scope Θ ls)

⊑-unlockedScope : (Θ : CtxMorph) → Δ ⊑ Δ′
  → unlockedScope Θ Δ ⊑ unlockedScope Θ Δ′
⊑-unlockedScope []             ls = ls
⊑-unlockedScope (bind A ∷ Θ)   ls = ⊑-unlockedScope Θ ls
⊑-unlockedScope (unlock X ∷ Θ) ls =
  ⊑-updateAt unmaskEnt unmaskEnt-comm unmaskEnt-mono (⊑-unlockedScope Θ ls)
⊑-unlockedScope (lock X ∷ Θ)   ls = ⊑-unlockedScope Θ ls

⊑-interior : (Θ : CtxMorph) → Δ ⊑ Δ′ → interior Θ Δ ⊑ interior Θ Δ′
⊑-interior Θ ls = ⊑-pushBinds (repsOf Θ) (⊑-scope Θ ls)

-- … and the same three transports for the LOCK-PRESERVING refinement,
-- the one a TERM travels along.
⊑ᵃ-scope : (Θ : CtxMorph) → Δ ⊑ᵃ Δ′ → scope Θ Δ ⊑ᵃ scope Θ Δ′
⊑ᵃ-scope []             ls = ls
⊑ᵃ-scope (bind A ∷ Θ)   ls = ⊑ᵃ-scope Θ ls
⊑ᵃ-scope (unlock X ∷ Θ) ls =
  ⊑ᵃ-updateAt unmaskEnt unmaskEnt-monoᵃ (⊑ᵃ-scope Θ ls)
⊑ᵃ-scope (lock X ∷ Θ)   ls =
  ⊑ᵃ-updateAt masked masked-monoᵃ (⊑ᵃ-scope Θ ls)

⊑ᵃ-interior : (Θ : CtxMorph) → Δ ⊑ᵃ Δ′ → interior Θ Δ ⊑ᵃ interior Θ Δ′
⊑ᵃ-interior Θ ls = ⊑ᵃ-pushBinds (repsOf Θ) (⊑ᵃ-scope Θ ls)

⊑-convCtx : (Θ : CtxMorph) → Δ ⊑ Δ′ → convCtx Θ Δ ⊑ convCtx Θ Δ′
⊑-convCtx Θ ls = ⊑-pushBinds (repsOf Θ) (⊑-unlockedScope Θ ls)

------------------------------------------------------------------------
-- 2.  Boundary well-formedness
------------------------------------------------------------------------

-- EVERY PREMISE IS READ ON THE FRAME THE ENTRY ACTS ON — the judgement is
-- SEQUENTIAL, in the order `scope` applies the list (head-LAST).  For the
-- tail Θ′ of the entry:
--
--   lock X    X is NAMEABLE in `scope Θ′ Δ`  (you may only mask what is
--             visible: no double masking, so `Locked` is one mask deep)
--   unlock X  X is LOCKED   in `scope Θ′ Δ`  (`Δ ∋lk X`: masked over a
--             nameable entry).  A VACUOUS UNLOCK — `↥X` at a slot the
--             frame leaves visible — IS REFUSED; it is the premise the
--             judgement used to drop, and the one the dual's restoring
--             `lock` needs (`mask-unmask`, strong.Ctx).
--   bind A    A is a type over `unlockedScope Θ′ Δ` — the tail's UNMASKS
--             applied and its LOCKS lifted.  A rep is never blocked by
--             the frame's own locks (that is the simultaneity law: a rep
--             is read where the CONVERSION is read, outside the masking
--             the boundary itself performs), and it may name what the
--             tail unlocked — which is what makes the scope move
--             (`_⋉_`, strong.Reduction) well formed.
--
-- Note the distinction the mask discipline forces: `unlock X`/`lock X`
-- NAME a masked index — that is an ENTRY, not a type — while `Δ ⊢ᵗ ` X`
-- at a masked slot is refused.  Tightness is about USE in a type, not
-- about mentioning the index in the context morphism.
--
-- `Δ ⊢ᵐ Θ` — the context morphism Θ is WELL FORMED over Δ.  An infix
-- judgement in the family of `Δ ⊢ᵗ A` (strong.Ctx) and `Δ ⊢ c ∶ A ⇝ B`
-- (strong.Conversion).
infix 4 _⊢ᵐ_
data _⊢ᵐ_ : Ctxᵗ → CtxMorph → Set where
  mw[] : Δ ⊢ᵐ []
  mw-b : ∀ {A Θ} → unlockedScope Θ Δ ⊢ᵗ A → Δ ⊢ᵐ Θ → Δ ⊢ᵐ (bind A ∷ Θ)
  mw-l : ∀ {X Θ} → scope Θ Δ ∋tv X → Δ ⊢ᵐ Θ → Δ ⊢ᵐ (lock X ∷ Θ)
  mw-u : ∀ {X Θ} → scope Θ Δ ∋lk X → Δ ⊢ᵐ Θ → Δ ⊢ᵐ (unlock X ∷ Θ)

-- THE TERM TRANSPORT IS `_⊑ᵃ_`, NOT `_⊑_`.  An `unlock X` CLAIMS that X
-- is locked, and `le-mu` — the clause that re-exposes a concealed slot —
-- destroys the claim; `_⊑ᵃ_` (strong.Ctx §4b) is `_⊑_` without it.
⊢ᵐ-⊑ᵃ : ∀ {Θ} → Δ ⊑ᵃ Δ′ → Δ ⊢ᵐ Θ → Δ′ ⊢ᵐ Θ
⊢ᵐ-⊑ᵃ {Θ = []}           ls mw[]        = mw[]
⊢ᵐ-⊑ᵃ {Θ = bind A ∷ Θ}   ls (mw-b w b)  =
  mw-b (⊑-wf (⊑-unlockedScope Θ (⊑ᵃ→⊑ ls)) w) (⊢ᵐ-⊑ᵃ ls b)
⊢ᵐ-⊑ᵃ {Θ = lock X ∷ Θ}   ls (mw-l tv b) =
  mw-l (⊑-tv (⊑-scope Θ (⊑ᵃ→⊑ ls)) tv) (⊢ᵐ-⊑ᵃ ls b)
⊢ᵐ-⊑ᵃ {Θ = unlock X ∷ Θ} ls (mw-u lk b) =
  mw-u (⊑ᵃ-lk (⊑ᵃ-scope Θ ls) lk) (⊢ᵐ-⊑ᵃ ls b)
