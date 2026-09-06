module strong.Terms where

-- Strong System F — the BOUNDARY and the TERMS.
--
-- A boundary is  M ⟪ Θ , c ⟫  with ONE frame change:
--
--   Θ : CtxMorph   the SCOPE SKELETON, rep-free except for binders
--        bind A   BINDS a fresh interior slot; A is its representation, read
--                in the PLAIN EXTERIOR (simultaneity: never through Θ's
--                other entries).  The only rep-carrying form; born once,
--                bound once.
--        lock X   MASKS exterior slot X: the interior may not NAME it.  The
--                entry is RETAINED on the type context — nothing is dropped and
--                nothing is re-spelled, so there is no demotion to perform.
--        unlock X   UNMASKS exterior slot X; it claims nothing, it merely
--                restores nameability.
--   c : Conv     the CONVERSION, checked on the CONVERSION CONTEXT (the
--                interior type context with Θ's bind masks lifted), where a
--                `seal X` can still resolve X at its binder.
--
-- Frames change ONLY at binders: `interior Θ Δ` is `Δ` with the masks applied
-- and Θ's binders pushed on.  There is no dropN, no cmax, no swapᵇ.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ; _[_]ᵗ)
open import strong.Ctx
open import strong.Conversion

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

------------------------------------------------------------------------
-- 3.  Terms
------------------------------------------------------------------------

infix  9 `_
infix  9 $_
infixl 7 _·_
infix  6 ƛ_∙_
infix  5 _⟪_,_⟫

data Term : Set where
  `_      : ℕ → Term
  $_      : ℕ → Term
  ƛ_∙_    : Ty → Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  _·[_,_] : Term → Ty → Ty → Term
  _⟪_,_⟫  : Term → CtxMorph → Conv → Term

Ctx : Set
Ctx = List Ty

infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → ℕ → Ty → Set where
  here  : ∀ {Γ A} → (A ∷ Γ) ∋ zero ⦂ A
  there : ∀ {Γ x A B} → Γ ∋ x ⦂ A → (B ∷ Γ) ∋ suc x ⦂ A

⤊ : Ctx → Ctx
⤊ Γ = map ⇑ᵗ Γ

------------------------------------------------------------------------
-- 4.  The typing judgment
------------------------------------------------------------------------

infix 3 _∣_⊢_⦂_
data _∣_⊢_⦂_ : Ctxᵗ → Ctx → Term → Ty → Set where

  ⊢` : ∀ {Δ Γ x A} → Γ ∋ x ⦂ A → Δ ∣ Γ ⊢ ` x ⦂ A

  ⊢$ : ∀ {Δ Γ n} → Δ ∣ Γ ⊢ $ n ⦂ `ℕ

  ⊢ƛ : ∀ {Δ Γ A B N} → Δ ⊢ᵗ A → Δ ∣ A ∷ Γ ⊢ N ⦂ B
     → Δ ∣ Γ ⊢ ƛ A ∙ N ⦂ (A ⇒ B)

  ⊢· : ∀ {Δ Γ A B L M} → Δ ∣ Γ ⊢ L ⦂ (A ⇒ B) → Δ ∣ Γ ⊢ M ⦂ A
     → Δ ∣ Γ ⊢ L · M ⦂ B

  ⊢Λ : ∀ {Δ Γ C N} → (abst ∷ Δ) ∣ ⤊ Γ ⊢ N ⦂ C → Δ ∣ Γ ⊢ Λ N ⦂ `∀ C

  ⊢·[] : ∀ {Δ Γ A B L} → Δ ∣ Γ ⊢ L ⦂ `∀ B → Δ ⊢ᵗ A
       → Δ ∣ Γ ⊢ L ·[ B , A ] ⦂ B [ A ]ᵗ

  -- (env).  ONE frame change.  The interior is term-closed and typed on the
  -- interior type context; the conversion is checked on the CONVERSION
  -- CONTEXT, where the boundary's binders and the slots it masks are both
  -- live; and its target type is the exterior type shifted past the
  -- boundary's binders.  Interior and conversion are both on the wrapper.
  env : ∀ {Δ Γ Θ c M Bᵢ Bₑ}
      → Δ ⊢ᵐ Θ
      → interior Θ Δ ∣ [] ⊢ M ⦂ Bᵢ
      → convCtx Θ Δ ⊢ c ∶ Bᵢ ⇝ shiftBy (numBinds Θ) Bₑ
      → Δ ⊢ᵗ Bₑ
        --------------------------------------------
      → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ

------------------------------------------------------------------------
-- 5.  Classification — ACTIVE / INERT, by the CONVERSION constructor
------------------------------------------------------------------------

-- Inert  = { s ↦ t , ∀ s , seal X , id-at-a-variable }
-- Active = { unseal X , id-at-base }
-- No source or target type is inspected and no slot arithmetic occurs.
data Inert : Conv → Set where
  I-idv  : ∀ {X}   → Inert (id (` X))
  I-seal : ∀ {X}   → Inert (seal X)
  I-fun  : ∀ {s t} → Inert (s ↦ t)
  I-all  : ∀ {s}   → Inert (`∀ s)

data Active : Conv → Set where
  A-idb    : ∀ {A} → Base A → Active (id A)
  A-unseal : ∀ {X} → Active (unseal X)

-- Totality over TYPED conversions: the payload restriction on `id` makes
-- classification a match on the TYPING derivation (the untypeable compound
-- identities are never classified at all).
act-or-inert : ∀ {Δ c A B} → Δ ⊢ c ∶ A ⇝ B → Active c ⊎ Inert c
act-or-inert (conv-id b)      = inj₁ (A-idb b)
act-or-inert (conv-idv tv)    = inj₂ I-idv
act-or-inert (conv-seal o)    = inj₂ I-seal
act-or-inert (conv-unseal o)  = inj₁ A-unseal
act-or-inert (conv-fun s t)   = inj₂ I-fun
act-or-inert (conv-all s)     = inj₂ I-all

act-not-inert : ∀ {c} → Active c → Inert c → ⊥
act-not-inert (A-idb ()) I-idv
act-not-inert A-unseal ()

------------------------------------------------------------------------
-- 6.  Values
------------------------------------------------------------------------

-- V-Λ carries `Value N`.  Reduction goes UNDER Λ (ξ-Λ in strong.Reduction),
-- so without this premise `Λ N` would be a value for every N and both
-- "values don't step" and determinism would be false — the defect the
-- IdLayerProbe machine-checked (notes/DECISIONS.md, repair 3).
data Value : Term → Set where
  V-$  : ∀ {n} → Value ($ n)
  V-ƛ  : ∀ {A N} → Value (ƛ A ∙ N)
  V-Λ  : ∀ {N} → Value N → Value (Λ N)
  V-⟪⟫ : ∀ {M Θ c} → Value M → Inert c → Value (M ⟪ Θ , c ⟫)

-- A value's variable type is VISIBLE on the value's bind type context, because
-- `env`'s last conjunct checks it there.  So a boundary can never conceal
-- the slot its bind conversion names.
value-var-visible : ∀ {Δ V X} → Value V → Δ ∣ [] ⊢ V ⦂ ` X → Δ ∋tv X
value-var-visible (V-⟪⟫ _ _) (env _ _ _ (wf-var tv)) = tv
