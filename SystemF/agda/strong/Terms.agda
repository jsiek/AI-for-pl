module strong.Terms where

-- Strong System F — the BOUNDARY and the TERMS.
--
-- A boundary is  M ⟪ Θ , c ⟫  with ONE frame change:
--
--   Θ : CtxMorph   the SCOPE SKELETON, rep-free except for owners
--        bind A   BINDS a fresh interior slot; A is its representation, read
--                in the PLAIN EXTERIOR (simultaneity: never through Θ's
--                other entries).  The only rep-carrying form; born once,
--                bound once.
--        lock X   MASKS exterior slot X: the interior may not NAME it.  The
--                entry is RETAINED on the type context — nothing is dropped and
--                nothing is re-spelled, so there is no demotion to perform.
--        unlock X   UNMASKS exterior slot X; it claims nothing, it merely
--                restores nameability.
--   c : Conv     the FACE, a conversion checked on the FACE TYPE CONTEXT (the
--                interior type context with Θ's bind masks lifted), where a
--                `seal X` can still resolve X at its owner.
--
-- Frames change ONLY at binders: `intC Θ Δ` is `Δ` with the masks applied
-- and Θ's owners pushed on.  There is no dropN, no cmax, no swapᵇ.

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

reps : CtxMorph → List Ty
reps []          = []
reps (bind A ∷ Θ) = A ∷ reps Θ
reps (unlock X ∷ Θ) = reps Θ
reps (lock X ∷ Θ) = reps Θ

-- `nbind` is the boundary's FRAME EXTENSION: the number of binders it adds.
-- It is the only surviving list arithmetic; cmax/dropN have no analogue,
-- because conceal masks in place.
nbind : CtxMorph → ℕ
nbind Θ = length (reps Θ)

-- The masks (`lock`) and unmasks (`unlock`), applied in place.
scp : CtxMorph → Ctxᵗ → Ctxᵗ
scp []          Δ = Δ
scp (bind A ∷ Θ) Δ = scp Θ Δ
scp (unlock X ∷ Θ) Δ = unmask X (scp Θ Δ)
scp (lock X ∷ Θ) Δ = mask X (scp Θ Δ)

-- The FACE type context: like `scp` but WITHOUT the conceal masks, so a `seal X`
-- can resolve X at its owner.  This is owner-syntactic lookup: the licence
-- is read on the type context that encloses the boundary, never inside it.
fscp : CtxMorph → Ctxᵗ → Ctxᵗ
fscp []          Δ = Δ
fscp (bind A ∷ Θ) Δ = fscp Θ Δ
fscp (unlock X ∷ Θ) Δ = unmask X (fscp Θ Δ)
fscp (lock X ∷ Θ) Δ = fscp Θ Δ

-- What replaces `intOf`: the same slot list, the interior mask, and the
-- owner extension.  Nothing is dropped and no rep is recomputed.
intC : CtxMorph → Ctxᵗ → Ctxᵗ
intC Θ Δ = prep (reps Θ) (scp Θ Δ)

fceC : CtxMorph → Ctxᵗ → Ctxᵗ
fceC Θ Δ = prep (reps Θ) (fscp Θ Δ)

-- The interior type context is the face type context with Θ's bind masks on, so anything
-- well formed inside is well formed on the face type context.
scp⊑fscp : (Θ : CtxMorph) (Δ : Ctxᵗ) → scp Θ Δ ⊑ fscp Θ Δ
scp⊑fscp []          Δ = ⊑-refl Δ
scp⊑fscp (bind A ∷ Θ) Δ = scp⊑fscp Θ Δ
scp⊑fscp (unlock X ∷ Θ) Δ = ⊑-upd unblk unblk-comm unblk-mono (scp⊑fscp Θ Δ)
scp⊑fscp (lock X ∷ Θ) Δ = mask-⊑ X (scp⊑fscp Θ Δ)

intC⊑fceC : (Θ : CtxMorph) (Δ : Ctxᵗ) → intC Θ Δ ⊑ fceC Θ Δ
intC⊑fceC Θ Δ = ⊑-prep (reps Θ) (scp⊑fscp Θ Δ)

⊑-scp : (Θ : CtxMorph) → Δ ⊑ Δ′ → scp Θ Δ ⊑ scp Θ Δ′
⊑-scp []          ls = ls
⊑-scp (bind A ∷ Θ) ls = ⊑-scp Θ ls
⊑-scp (unlock X ∷ Θ) ls = ⊑-upd unblk unblk-comm unblk-mono (⊑-scp Θ ls)
⊑-scp (lock X ∷ Θ) ls = ⊑-upd blk blk-comm blk-mono (⊑-scp Θ ls)

⊑-fscp : (Θ : CtxMorph) → Δ ⊑ Δ′ → fscp Θ Δ ⊑ fscp Θ Δ′
⊑-fscp []          ls = ls
⊑-fscp (bind A ∷ Θ) ls = ⊑-fscp Θ ls
⊑-fscp (unlock X ∷ Θ) ls = ⊑-upd unblk unblk-comm unblk-mono (⊑-fscp Θ ls)
⊑-fscp (lock X ∷ Θ) ls = ⊑-fscp Θ ls

⊑-intC : (Θ : CtxMorph) → Δ ⊑ Δ′ → intC Θ Δ ⊑ intC Θ Δ′
⊑-intC Θ ls = ⊑-prep (reps Θ) (⊑-scp Θ ls)

⊑-fceC : (Θ : CtxMorph) → Δ ⊑ Δ′ → fceC Θ Δ ⊑ fceC Θ Δ′
⊑-fceC Θ ls = ⊑-prep (reps Θ) (⊑-fscp Θ ls)

------------------------------------------------------------------------
-- 2.  Boundary well-formedness
------------------------------------------------------------------------

-- Every premise names a slot or checks a rep in the PLAIN exterior.  There
-- is no Reversal≈, no starOnly, no SkelEq, no x-lookup: an `unlock` claims
-- nothing at all, and a `lock` claims nothing either — the claim lives in the
-- FACE (`seal X`, which must cite a live owner).
--
-- An `unlock X` premise asks only that the slot EXISTS.  It cannot ask that the
-- slot be masked and stay stable under refinement (a Cancel may already have
-- un-masked it), and it need not: `unmask` is total and an alias at an
-- un-masked slot is a no-op.  Note the distinction the mask discipline
-- forces: `unlock X`/`lock X` NAME a masked index — that is an ENTRY, not a type
-- — while `Δ ⊢ᵗ ` X` at a masked slot is refused.  Tightness is about USE in
-- a type, not about mentioning the index in the context morphism.
data Bwf (Δ : Ctxᵗ) : CtxMorph → Set where
  bw[] : Bwf Δ []
  bw-b : ∀ {A Θ} → Δ ⊢ᵗ A → Bwf Δ Θ → Bwf Δ (bind A ∷ Θ)
  bw-l : ∀ {X Θ} → Δ ∋tv X → Bwf Δ Θ → Bwf Δ (lock X ∷ Θ)
  bw-u : ∀ {X E Θ} → Δ ∋e X , E → Bwf Δ Θ → Bwf Δ (unlock X ∷ Θ)

Bwf-⊑ : ∀ {Θ} → Δ ⊑ Δ′ → Bwf Δ Θ → Bwf Δ′ Θ
Bwf-⊑ ls bw[]        = bw[]
Bwf-⊑ ls (bw-b w b)  = bw-b (⊑-wf ls w) (Bwf-⊑ ls b)
Bwf-⊑ ls (bw-l tv b) = bw-l (⊑-tv ls tv) (Bwf-⊑ ls b)
Bwf-⊑ ls (bw-u d b)  with ⊑-∋e ls d
... | E′ , d′ , _ = bw-u d′ (Bwf-⊑ ls b)

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
  -- interior type context; the face conversion is checked on the FACE type context, where
  -- the boundary's owners and the slots it masks are both live; the exterior
  -- face is a type over the plain exterior.  Both faces are on the wrapper.
  env : ∀ {Δ Γ Θ c M Bᵢ Bₑ p}
      → Bwf Δ Θ
      → intC Θ Δ ∣ [] ⊢ M ⦂ Bᵢ
      → fceC Θ Δ ⊢ c ∶ Bᵢ ⇝ liftN (nbind Θ) Bₑ ∙ p
      → Δ ⊢ᵗ Bₑ
        --------------------------------------------
      → Δ ∣ Γ ⊢ M ⟪ Θ , c ⟫ ⦂ Bₑ

------------------------------------------------------------------------
-- 5.  Classification — ACTIVE / INERT, by the CONVERSION constructor
------------------------------------------------------------------------

-- Inert  = { s ↦ t , ∀ s , seal X , id-at-a-variable }
-- Active = { unseal X , id-at-base }
-- No face type is inspected and no slot arithmetic occurs.
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
act-or-inert : ∀ {Δ c A B p} → Δ ⊢ c ∶ A ⇝ B ∙ p → Active c ⊎ Inert c
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
-- the slot its bind face names.
value-var-visible : ∀ {Δ V X} → Value V → Δ ∣ [] ⊢ V ⦂ ` X → Δ ∋tv X
value-var-visible (V-⟪⟫ _ _) (env _ _ _ (wf-var tv)) = tv
