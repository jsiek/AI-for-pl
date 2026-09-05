module strong.Terms where

-- Strong System F — the BOUNDARY and the TERMS.
--
-- A boundary is  M ⟪ Θ , c ⟫  with ONE frame change:
--
--   Θ : BCtx   the SCOPE SKELETON, rep-free except for owners
--        own A   BINDS a fresh interior slot; A is its representation, read
--                in the PLAIN EXTERIOR (simultaneity: never through Θ's
--                other entries).  The only rep-carrying form; born once,
--                bound once.
--        cnc X   MASKS exterior slot X: the interior may not NAME it.  The
--                entry is RETAINED on the spine — nothing is dropped and
--                nothing is re-spelled, so there is no demotion to perform.
--        ali X   UNMASKS exterior slot X; it claims nothing, it merely
--                restores nameability.
--   c : Conv     the FACE, a conversion checked on the FACE SPINE (the
--                interior spine with Θ's own masks lifted), where a
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
-- 1.  The boundary skeleton
------------------------------------------------------------------------

data BEnt : Set where
  own : Ty → BEnt      -- BINDS a fresh slot at rep A (A over the exterior)
  ali : ℕ → BEnt       -- unmask exterior slot X   (name only)
  cnc : ℕ → BEnt       -- mask   exterior slot X   (name only)

BCtx : Set
BCtx = List BEnt

reps : BCtx → List Ty
reps []          = []
reps (own A ∷ Θ) = A ∷ reps Θ
reps (ali X ∷ Θ) = reps Θ
reps (cnc X ∷ Θ) = reps Θ

-- `nrev` is the boundary's FRAME EXTENSION: the number of binders it adds.
-- It is the only surviving list arithmetic; cmax/dropN have no analogue,
-- because conceal masks in place.
nrev : BCtx → ℕ
nrev Θ = length (reps Θ)

-- The masks (`cnc`) and unmasks (`ali`), applied in place.
scp : BCtx → Ctxᵗ → Ctxᵗ
scp []          Δ = Δ
scp (own A ∷ Θ) Δ = scp Θ Δ
scp (ali X ∷ Θ) Δ = unmask X (scp Θ Δ)
scp (cnc X ∷ Θ) Δ = mask X (scp Θ Δ)

-- The FACE spine: like `scp` but WITHOUT the conceal masks, so a `seal X`
-- can resolve X at its owner.  This is owner-syntactic lookup: the licence
-- is read on the spine that encloses the boundary, never inside it.
fscp : BCtx → Ctxᵗ → Ctxᵗ
fscp []          Δ = Δ
fscp (own A ∷ Θ) Δ = fscp Θ Δ
fscp (ali X ∷ Θ) Δ = unmask X (fscp Θ Δ)
fscp (cnc X ∷ Θ) Δ = fscp Θ Δ

-- What replaces `intOf`: the same slot list, the interior mask, and the
-- owner extension.  Nothing is dropped and no rep is recomputed.
intC : BCtx → Ctxᵗ → Ctxᵗ
intC Θ Δ = prep (reps Θ) (scp Θ Δ)

fceC : BCtx → Ctxᵗ → Ctxᵗ
fceC Θ Δ = prep (reps Θ) (fscp Θ Δ)

-- The interior spine is the face spine with Θ's own masks on, so anything
-- well formed inside is well formed on the face spine.
scp⊑fscp : (Θ : BCtx) (Δ : Ctxᵗ) → scp Θ Δ ⊑ fscp Θ Δ
scp⊑fscp []          Δ = ⊑-refl Δ
scp⊑fscp (own A ∷ Θ) Δ = scp⊑fscp Θ Δ
scp⊑fscp (ali X ∷ Θ) Δ = ⊑-upd unblk unblk-comm unblk-mono (scp⊑fscp Θ Δ)
scp⊑fscp (cnc X ∷ Θ) Δ = mask-⊑ X (scp⊑fscp Θ Δ)

intC⊑fceC : (Θ : BCtx) (Δ : Ctxᵗ) → intC Θ Δ ⊑ fceC Θ Δ
intC⊑fceC Θ Δ = ⊑-prep (reps Θ) (scp⊑fscp Θ Δ)

⊑-scp : (Θ : BCtx) → Δ ⊑ Δ′ → scp Θ Δ ⊑ scp Θ Δ′
⊑-scp []          ls = ls
⊑-scp (own A ∷ Θ) ls = ⊑-scp Θ ls
⊑-scp (ali X ∷ Θ) ls = ⊑-upd unblk unblk-comm unblk-mono (⊑-scp Θ ls)
⊑-scp (cnc X ∷ Θ) ls = ⊑-upd blk blk-comm blk-mono (⊑-scp Θ ls)

⊑-fscp : (Θ : BCtx) → Δ ⊑ Δ′ → fscp Θ Δ ⊑ fscp Θ Δ′
⊑-fscp []          ls = ls
⊑-fscp (own A ∷ Θ) ls = ⊑-fscp Θ ls
⊑-fscp (ali X ∷ Θ) ls = ⊑-upd unblk unblk-comm unblk-mono (⊑-fscp Θ ls)
⊑-fscp (cnc X ∷ Θ) ls = ⊑-fscp Θ ls

⊑-intC : (Θ : BCtx) → Δ ⊑ Δ′ → intC Θ Δ ⊑ intC Θ Δ′
⊑-intC Θ ls = ⊑-prep (reps Θ) (⊑-scp Θ ls)

⊑-fceC : (Θ : BCtx) → Δ ⊑ Δ′ → fceC Θ Δ ⊑ fceC Θ Δ′
⊑-fceC Θ ls = ⊑-prep (reps Θ) (⊑-fscp Θ ls)

------------------------------------------------------------------------
-- 2.  Boundary well-formedness
------------------------------------------------------------------------

-- Every premise names a slot or checks a rep in the PLAIN exterior.  There
-- is no Reversal≈, no starOnly, no SkelEq, no x-lookup: an `ali` claims
-- nothing at all, and a `cnc` claims nothing either — the claim lives in the
-- FACE (`seal X`, which must cite a live owner).
--
-- An `ali X` premise asks only that the slot EXISTS.  It cannot ask that the
-- slot be masked and stay stable under refinement (a Cancel may already have
-- un-masked it), and it need not: `unmask` is total and an alias at an
-- un-masked slot is a no-op.  Note the distinction the mask discipline
-- forces: `ali X`/`cnc X` NAME a masked index — that is an ENTRY, not a type
-- — while `Δ ⊢ᵗ ` X` at a masked slot is refused.  Tightness is about USE in
-- a type, not about mentioning the index in the skeleton.
data Bwf (Δ : Ctxᵗ) : BCtx → Set where
  bw[] : Bwf Δ []
  bw-o : ∀ {A Θ} → Δ ⊢ᵗ A → Bwf Δ Θ → Bwf Δ (own A ∷ Θ)
  bw-c : ∀ {X Θ} → Δ ∋tv X → Bwf Δ Θ → Bwf Δ (cnc X ∷ Θ)
  bw-a : ∀ {X E Θ} → Δ ∋e X , E → Bwf Δ Θ → Bwf Δ (ali X ∷ Θ)

Bwf-⊑ : ∀ {Θ} → Δ ⊑ Δ′ → Bwf Δ Θ → Bwf Δ′ Θ
Bwf-⊑ ls bw[]        = bw[]
Bwf-⊑ ls (bw-o w b)  = bw-o (⊑-wf ls w) (Bwf-⊑ ls b)
Bwf-⊑ ls (bw-c tv b) = bw-c (⊑-tv ls tv) (Bwf-⊑ ls b)
Bwf-⊑ ls (bw-a d b)  with ⊑-∋e ls d
... | E′ , d′ , _ = bw-a d′ (Bwf-⊑ ls b)

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
  _⟪_,_⟫  : Term → BCtx → Conv → Term

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
  -- interior spine; the face conversion is checked on the FACE spine, where
  -- the boundary's owners and the slots it masks are both live; the exterior
  -- face is a type over the plain exterior.  Both faces are on the wrapper.
  env : ∀ {Δ Γ Θ c M Bᵢ Bₑ p}
      → Bwf Δ Θ
      → intC Θ Δ ∣ [] ⊢ M ⦂ Bᵢ
      → fceC Θ Δ ⊢ c ∶ Bᵢ ⇝ liftN (nrev Θ) Bₑ ∙ p
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

-- A value's variable type is VISIBLE on the value's own spine, because
-- `env`'s last conjunct checks it there.  So a boundary can never conceal
-- the slot its own face names.
value-var-visible : ∀ {Δ V X} → Value V → Δ ∣ [] ⊢ V ⦂ ` X → Δ ∋tv X
value-var-visible (V-⟪⟫ _ _) (env _ _ _ (wf-var tv)) = tv
