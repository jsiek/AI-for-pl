module strong.Boundary where

-- Tight, dual boundary — typing, on the BOUNDARY-TYPE (B₀) formulation.
--
--   reveal  X:=A :  X fresh INTERNAL var;  A (rep) EXTERNAL to the boundary,
--                   read in the PLAIN exterior Γ — with no interference from
--                   the boundary's other entries (Jeremy's ruling,
--                   notes/DECISIONS.md "RULING — telescopic (bwf-↑)
--                   REVERTED").  This is the SIMULTANEITY of a boundary:
--                     (i)  a conceal's rep MAY mention the boundary's reveal
--                          variables (the original Example-8 fix), and
--                     (ii) a reveal's rep is read in the plain exterior,
--                          independent of its siblings.
--                   The two directions are not symmetric because the two
--                   blocks face opposite ways, but each block is read
--                   SIMULTANEOUSLY: no reveal is read over another.
--   reveal  X:⋆   :  a REP-LESS abstract reveal (constructor `rvl⋆`).  It
--                   contributes an `abst` interior entry, carries no
--                   knowledge, and its `baseS` slot is `blk`, so no Scoped
--                   type ever names it; its ρᵇ image is a dummy (`ℕ) that is
--                   therefore never consulted.  Produced by the ambient dual
--                   at a Λ-BOUND slot the boundary drops without concealing.
--   conceal Y:=A :  Y EXTERNAL var;         A (rep) INTERNAL to the boundary.
--
-- TIGHT: a conceal restricts the interior to Y's existential scope (Γ ↓ Y); a
-- reveal adds a fresh var carrying the INTERIOR READING ⟦A⟧ of its rep as its
-- knowledge (Decision 1's 2026-09-04 refinement) — or `abst` when that reading
-- is not a legitimate telescope entry.  A wrapper  M ⟪ Θ , B₀ ⟫  records the
-- BOUNDARY type B₀; the internal and external types are its two projections:
--
--   internal = substᵗ (γᵇ Θ) B₀       -- conceals resolved to their reps
--   external = substᵗ (ρᵇ Θ) B₀       -- reveals  resolved to their reps
--
-- so there is NO consistency premise — both faces come from one B₀ (the (env)
-- rule we chose, not the looser τ(A)=σ(B) form).
--
-- A conceal is licensed in the REVERSAL FORM (Decision 3's ruling, probe
-- notes/old/ReversalProbe.agda): its rep, READ BACK OUT through the whole
-- boundary, must be the exterior's own knowledge about the concealed
-- variable.  Because that premise mentions the WHOLE boundary, boundary
-- well-formedness carries Θ as a parameter and recurses on a suffix.

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_)
open import Data.Nat.Properties using (_≟_)
open import Data.Nat using (_<?_; _≤?_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Relation.Nullary using (yes; no; ⌊_⌋)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)
open import strong.Types
open import strong.TypeSubst using (_⨟ᵗ_)
open import strong.Context
  using (TCtx; TyEntry; abst; rvld; _↓_; _⊢_;
         wf-var; wf-ℕ; wf-𝔹; wf-⇒; wf-∀;
         _∋tv_; here-abst; here-rvld; skip-abst; skip-rvld;
         _∋_:=_; here; ∋:=→∋tv;
         Ctx; _∋_⦂_; there; ⤊)

------------------------------------------------------------------------
-- Boundary
------------------------------------------------------------------------

data BEntry : Set where
  rvl  : Ty → BEntry      -- reveal a fresh internal var;  A = external rep
  rvl⋆ : BEntry           -- reveal a fresh ABSTRACT internal var; no rep
  cnc  : ℕ → Ty → BEntry  -- conceal external var at index X;  A = int. rep

BCtx : Set
BCtx = List BEntry

-- Conceal indices are WHOLE-Γ relative: the interior is everything DEEPER than
-- the deepest conceal (Γ ↓ cmax), with the reveal variables prepended.  This
-- "whole-Γ" projection keeps conceal indices uniform (no progressive shifting),
-- which is what makes renaming/substitution tractable.

revs : BCtx → ℕ                 -- number of reveals (rvl and rvl⋆ alike)
revs []            = 0
revs (rvl A ∷ Θ)   = suc (revs Θ)
revs (rvl⋆ ∷ Θ)    = suc (revs Θ)
revs (cnc X A ∷ Θ) = revs Θ

cmax : BCtx → ℕ                 -- 1 + (max conceal index), 0 if no conceals
cmax []            = 0
cmax (rvl A ∷ Θ)   = cmax Θ
cmax (rvl⋆ ∷ Θ)    = cmax Θ
cmax (cnc X A ∷ Θ) = suc X ⊔ cmax Θ

dropN : ℕ → TCtx → TCtx         -- drop the first n (shallowest) entries
dropN zero    Γ       = Γ
dropN (suc n) []      = []
dropN (suc n) (E ∷ Γ) = dropN n Γ

prepAbst : ℕ → TCtx → TCtx      -- prepend n fresh abstract variables
prepAbst zero    Γ = Γ
prepAbst (suc n) Γ = abst ∷ prepAbst n Γ

-- ρᵇ : reveal-resolve, the EXTERNAL face.  PARALLEL (simultaneous): a
-- reveal's rep is a type over the plain exterior, so it is substituted AS
-- STORED — never folded through the boundary's other reveals.  Conceals leave
-- the exterior unchanged, and the exterior passes through (shifted below the
-- reveal vars).  A rep-less reveal gets a DUMMY image; (env)'s scope premise
-- (baseS marks its slot `blk`) keeps any Scoped type from naming it.
ρᵇ : BCtx → Substᵗ
ρᵇ []            = `_
ρᵇ (rvl A ∷ Θ)   = A •ᵗ ρᵇ Θ
ρᵇ (rvl⋆ ∷ Θ)    = `ℕ •ᵗ ρᵇ Θ
ρᵇ (cnc X A ∷ Θ) = ρᵇ Θ

-- γᵇ : conceal-resolve, on the boundary frame (reveals ++ Γ, reveals shallow).
-- A reveal var (bframe index < revs) passes through unchanged.  For a
-- Γ-index i: a concealed index ↦ its rep (already over the WHOLE
-- interior — NOT shifted, so a
-- rep may mention a reveal var), a DEEPER (kept) index ↦ its interior slot
-- ` (revs + (i ∸ cmax)).
sover : ℕ → Ty → Substᵗ → Substᵗ    -- override index X with A, else σ
sover X A σ Y with X ≟ Y
sover X A σ Y | yes _ = A
sover X A σ Y | no  _ = σ Y

γcnc : ℕ → ℕ → BCtx → Substᵗ        -- r=revs, m=cmax : resolve a Γ-index i
γcnc r m []            = λ i → ` (r + (i ∸ m))
γcnc r m (rvl A ∷ Θ)   = γcnc r m Θ
γcnc r m (rvl⋆ ∷ Θ)    = γcnc r m Θ
γcnc r m (cnc X A ∷ Θ) = sover X A (γcnc r m Θ)

prepId : ℕ → Substᵗ → Substᵗ        -- first r indices identity, NO output shift
prepId r σ j with j <? r
prepId r σ j | yes _ = ` j
prepId r σ j | no  _ = σ (j ∸ r)

γᵇ : BCtx → Substᵗ
γᵇ Θ = prepId (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ)

------------------------------------------------------------------------
-- Boundary-type scope.  A "blocked" bframe slot — a Γ-index shallower than cmax
-- that is not itself concealed, or the slot of a REP-LESS reveal — has no
-- honest image under one of the two faces; γᵇ would silently alias the former
-- onto a kept var and ρᵇ hands the latter a dummy.  The (env) rule forbids B₀
-- from naming a blocked slot: it must be Scoped over the accessibility stack,
-- in which blocked slots are `blk`.
------------------------------------------------------------------------

data Slot : Set where ok blk : Slot

SCtx : Set
SCtx = List Slot

data _∋ok_ : SCtx → ℕ → Set where
  hereᵒ  : ∀ {Ψ}         →              (ok ∷ Ψ) ∋ok zero
  thereᵒ : ∀ {s Ψ X} → Ψ ∋ok X → (s ∷ Ψ) ∋ok suc X

data Scoped : SCtx → Ty → Set where
  sc-var : ∀ {Ψ X} → Ψ ∋ok X       → Scoped Ψ (` X)
  sc-ℕ   : ∀ {Ψ}                    → Scoped Ψ `ℕ
  sc-𝔹   : ∀ {Ψ}                    → Scoped Ψ `𝔹
  sc-⇒   : ∀ {Ψ A B} → Scoped Ψ A → Scoped Ψ B → Scoped Ψ (A ⇒ B)
  sc-∀   : ∀ {Ψ A}   → Scoped (ok ∷ Ψ) A        → Scoped Ψ (`∀ A)

isConc : ℕ → BCtx → Bool             -- is i a conceal index of Θ?
isConc i []            = false
isConc i (rvl _ ∷ Θ)   = isConc i Θ
isConc i (rvl⋆ ∷ Θ)    = isConc i Θ
isConc i (cnc X _ ∷ Θ) = ⌊ i ≟ X ⌋ ∨ isConc i Θ

-- Γ-index i : kept (≥ cmax) or concealed → ok
slotAt : BCtx → ℕ → Slot
slotAt Θ i with cmax Θ ≤? i
slotAt Θ i | yes _ = ok
slotAt Θ i | no  _ = if isConc i Θ then ok else blk

slotsᴳ : BCtx → ℕ → TCtx → SCtx      -- slots for Γ from index i onward
slotsᴳ Θ i []      = []
slotsᴳ Θ i (_ ∷ Γ) = slotAt Θ i ∷ slotsᴳ Θ (suc i) Γ

-- the reveal prefix, PER ENTRY: a real reveal is accessible, a rep-less one
-- is not (its external face is a dummy)
revSlots : BCtx → SCtx
revSlots []            = []
revSlots (rvl A ∷ Θ)   = ok ∷ revSlots Θ
revSlots (rvl⋆ ∷ Θ)    = blk ∷ revSlots Θ
revSlots (cnc X A ∷ Θ) = revSlots Θ

len-revSlots : ∀ Θ → length (revSlots Θ) ≡ revs Θ
len-revSlots []            = refl
len-revSlots (rvl A ∷ Θ)   = cong suc (len-revSlots Θ)
len-revSlots (rvl⋆ ∷ Θ)    = cong suc (len-revSlots Θ)
len-revSlots (cnc X A ∷ Θ) = len-revSlots Θ

-- the accessibility stack for B₀ over the boundary frame
baseS : BCtx → TCtx → SCtx
baseS Θ Γ = revSlots Θ ++ slotsᴳ Θ 0 Γ

-- scope-restricted subst-cong: two substitutions agreeing on the
-- accessible slots
-- act the same on a Scoped type (blocked slots are irrelevant).
subst-cong-sc : ∀ {Ψ}{σ τ : Substᵗ} {A}
  → Scoped Ψ A → (∀ X → Ψ ∋ok X → σ X ≡ τ X) → substᵗ σ A ≡ substᵗ τ A
subst-cong-sc (sc-var p) h = h _ p
subst-cong-sc sc-ℕ h = refl
subst-cong-sc sc-𝔹 h = refl
subst-cong-sc (sc-⇒ sA sB) h =
  cong₂ _⇒_ (subst-cong-sc sA h) (subst-cong-sc sB h)
subst-cong-sc {Ψ}{σ}{τ} (sc-∀ sA) h = cong `∀ (subst-cong-sc sA h-ext)
  where
    h-ext : ∀ X → (ok ∷ Ψ) ∋ok X → extsᵗ σ X ≡ extsᵗ τ X
    h-ext zero    hereᵒ      = refl
    h-ext (suc X) (thereᵒ p) = cong (renameᵗ suc) (h X p)

------------------------------------------------------------------------
-- KNOWLEDGE INTERIORS.  The interior context prepends, per reveal, the
-- INTERIOR READING ⟦A⟧ of its rep as a knowledge entry (Decision 1's
-- 2026-09-04 refinement).  Two total guards send a reveal to `abst` instead:
--
--   bfree : the rep names a slot the boundary BLOCKS — then its reading is
--           not a type of the interior at all;
--   dfree : the reading names a reveal slot at or ABOVE this one — then it
--           is not a legitimate TELESCOPE entry (Context.agda reads a `rvld`
--           rep over its own tail), and the down-shift dnT would truncate it.
--
-- Under the PARALLEL reading the rep A of a reveal sits over the plain
-- exterior, so its reading involves only EXTERIOR variables: a concealed one
-- goes to its rep (γcnc), a kept one to its interior slot.  A rep therefore
-- never names a sibling reveal variable — but its READING can still reach
-- one, because a conceal's rep may (simultaneity (i)); that is why the dfree
-- guard survives the revert.  dnT (suc j) moves the reading down to the
-- entry's own tail.
------------------------------------------------------------------------

isOk : Slot → Bool
isOk ok  = true
isOk blk = false

-- bfree Θ d A : A (an EXTERIOR type, under d binders) names no BLOCKED slot
-- of Θ
bfree : BCtx → ℕ → Ty → Bool
bfree Θ d (` X)   = ⌊ X <? d ⌋ ∨ isOk (slotAt Θ (X ∸ d))
bfree Θ d `ℕ      = true
bfree Θ d `𝔹      = true
bfree Θ d (A ⇒ B) = bfree Θ d A ∧ bfree Θ d B
bfree Θ d (`∀ A)  = bfree Θ (suc d) A

-- dfree b d T : T has no FREE index below d (b counts the binders passed, so
-- the forbidden window is [b , b + d)).  Where it holds, dnT d loses nothing.
dfree : ℕ → ℕ → Ty → Bool
dfree b d (` X)   = ⌊ X <? b ⌋ ∨ ⌊ b + d ≤? X ⌋
dfree b d `ℕ      = true
dfree b d `𝔹      = true
dfree b d (A ⇒ B) = dfree b d A ∧ dfree b d B
dfree b d (`∀ A)  = dfree (suc b) d A

dnT : ℕ → Ty → Ty                     -- shift down past k entries
dnT k = renameᵗ (_∸ k)

-- rdSub Θ : the reading map for an EXTERIOR type, into the WHOLE interior
-- of Θ.  Parallel: no reveal-slot window to skip, so it is γcnc itself.
rdSub : BCtx → Substᵗ
rdSub Θ = γcnc (revs Θ) (cmax Θ) Θ

rawRead : BCtx → Ty → Ty
rawRead Θ A = substᵗ (rdSub Θ) A

-- ⟦ Θ ⟧ᵉ j A : the interior ENTRY of the reveal at slot j whose rep is A
⟦_⟧ᵉ : BCtx → ℕ → Ty → TyEntry
⟦ Θ ⟧ᵉ j A =
  if bfree Θ 0 A ∧ dfree 0 (suc j) (rawRead Θ A)
  then rvld (dnT (suc j) (rawRead Θ A))
  else abst

revEnts : BCtx → ℕ → BCtx → TCtx
revEnts Θ j []            = []
revEnts Θ j (rvl A ∷ Ξ)   = ⟦ Θ ⟧ᵉ j A ∷ revEnts Θ (suc j) Ξ
revEnts Θ j (rvl⋆ ∷ Ξ)    = abst ∷ revEnts Θ (suc j) Ξ
revEnts Θ j (cnc X A ∷ Ξ) = revEnts Θ j Ξ

len-revEnts : ∀ Θ j Ξ → length (revEnts Θ j Ξ) ≡ revs Ξ
len-revEnts Θ j []            = refl
len-revEnts Θ j (rvl A ∷ Ξ)   = cong suc (len-revEnts Θ (suc j) Ξ)
len-revEnts Θ j (rvl⋆ ∷ Ξ)    = cong suc (len-revEnts Θ (suc j) Ξ)
len-revEnts Θ j (cnc X A ∷ Ξ) = len-revEnts Θ j Ξ

-- interior context: the reveal block's knowledge entries, then everything
-- deeper than the deepest conceal
intOf : TCtx → BCtx → TCtx
intOf Γ Θ = revEnts Θ 0 Θ ++ dropN (cmax Θ) Γ

------------------------------------------------------------------------
-- THE REVERSAL PREMISE (notes/DECISIONS.md, Decision 3's ruling).
--
-- outRead Θ A reads an INTERIOR type back out to the exterior: a reveal
-- variable ↦ its external face (its rep as stored, the parallel reading), a
-- kept interior variable ↦ its exterior index.  A conceal ↓X:=A is licensed
-- when that read-back is exactly the exterior's knowledge about X — which,
-- since Context.agda's ∋:= is tail-relative, is A₀ lifted by upRep X.
------------------------------------------------------------------------

outSub : BCtx → Substᵗ
outSub Θ X with X <? revs Θ
outSub Θ X | yes _ = ρᵇ Θ X
outSub Θ X | no  _ = ` (cmax Θ + (X ∸ revs Θ))

outRead : BCtx → Ty → Ty              -- interior type ↦ exterior type
outRead Θ A = substᵗ (outSub Θ) A

upRep : ℕ → Ty → Ty                   -- (Γ ↓ X)-type ↦ Γ-type
upRep X A₀ = renameᵗ (λ i → suc X + i) A₀

Reversal : BCtx → ℕ → Ty → Ty → Set
Reversal Θ X A A₀ = outRead Θ A ≡ upRep X A₀

------------------------------------------------------------------------
-- Boundary well-formedness.  The reveal block is read SIMULTANEOUSLY: every
-- reveal's rep is well formed in the PLAIN exterior Γ, with no interference
-- from the boundary's other entries.  The conceal premise is the REVERSAL
-- form and mentions the whole boundary, so Θ is still a parameter and the
-- recursion runs on a suffix Ξ.
------------------------------------------------------------------------

data Bwf (Γ Ψ : TCtx) (Θ : BCtx) : BCtx → Set where
  bwf[] : Bwf Γ Ψ Θ []
  bwf↑  : ∀ {A Ξ} → Γ ⊢ A
        → Bwf Γ Ψ Θ Ξ → Bwf Γ Ψ Θ (rvl A ∷ Ξ)
  bwf⋆  : ∀ {Ξ} → Bwf Γ Ψ Θ Ξ → Bwf Γ Ψ Θ (rvl⋆ ∷ Ξ)
  bwf↓  : ∀ {X A A₀ Ξ}
        → Γ ∋ X := A₀ → Reversal Θ X A A₀ → Ψ ⊢ A
        → Bwf Γ Ψ Θ Ξ → Bwf Γ Ψ Θ (cnc X A ∷ Ξ)

infix 4 _∣_⊢ᵇ_
_∣_⊢ᵇ_ : TCtx → TCtx → BCtx → Set
Γ ∣ Ψ ⊢ᵇ Θ = Bwf Γ Ψ Θ Θ

------------------------------------------------------------------------
-- Terms and typing
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
  _⟪_,_⟫  : Term → BCtx → Ty → Term      -- M wrapped in Θ, BOUNDARY type B₀

private
  variable
    Δ Γ : TCtx
    Γₜ : Ctx
    A B C B₀ : Ty
    L M N : Term
    Θ : BCtx
    x n X : ℕ

infix 3 _∣_⊢_⦂_
data _∣_⊢_⦂_ : TCtx → Ctx → Term → Ty → Set where

  ⊢` : Γₜ ∋ x ⦂ A → Δ ∣ Γₜ ⊢ ` x ⦂ A
  ⊢$ : Δ ∣ Γₜ ⊢ $ n ⦂ `ℕ
  ⊢ƛ : Δ ⊢ A → Δ ∣ A ∷ Γₜ ⊢ N ⦂ B → Δ ∣ Γₜ ⊢ ƛ A ∙ N ⦂ (A ⇒ B)
  ⊢· : Δ ∣ Γₜ ⊢ L ⦂ (A ⇒ B) → Δ ∣ Γₜ ⊢ M ⦂ A → Δ ∣ Γₜ ⊢ L · M ⦂ B
  ⊢Λ : (abst ∷ Δ) ∣ ⤊ Γₜ ⊢ N ⦂ C → Δ ∣ Γₜ ⊢ Λ N ⦂ `∀ C
  ⊢·[] : Δ ∣ Γₜ ⊢ L ⦂ `∀ B → Δ ⊢ A → Δ ∣ Γₜ ⊢ L ·[ B , A ] ⦂ B [ A ]ᵗ

  -- (env): record the BOUNDARY type B₀; internal = B₀[γ], external = B₀[ρ].
  -- B₀ must be Scoped over the accessibility stack (it may not name a
  -- blocked slot).
  env : Δ ∣ intOf Δ Θ ⊢ᵇ Θ
      → Scoped (baseS Θ Δ) B₀
      → intOf Δ Θ ∣ [] ⊢ M ⦂ substᵗ (γᵇ Θ) B₀
        ---------------------------------------------------
      → Δ ∣ Γₜ ⊢ M ⟪ Θ , B₀ ⟫ ⦂ substᵗ (ρᵇ Θ) B₀

------------------------------------------------------------------------
-- Example 8 (spurious conceal):  B₀ = Z→Z ;  internal Z→Z, external Y→Y
--   Θ₈'s reveal rep is ` 0 (= Y, a BLOCKED slot), so Z's interior entry is
--   `abst` — the reveal carries no knowledge.
------------------------------------------------------------------------

Γ₈ : TCtx
Γ₈ = abst ∷ rvld `ℕ ∷ []

Θ₈ : BCtx
Θ₈ = cnc 1 `ℕ ∷ rvl (` 0) ∷ []

_ : intOf Γ₈ Θ₈ ≡ abst ∷ []
_ = refl

_ : Γ₈ ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ Θ₈ , (` 0 ⇒ ` 0) ⟫ ⦂ (` 0 ⇒ ` 0)
_ = env (bwf↓ (skip-abst here) refl wf-ℕ (bwf↑ (wf-var here-abst) bwf[]))
        (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
        (⊢ƛ (wf-var here-abst) (⊢` here))

------------------------------------------------------------------------
-- Example 1 (NON-spurious conceal):  B₀ = X ;  external X, internal ℕ
------------------------------------------------------------------------

_ : (rvld `ℕ ∷ []) ∣ [] ⊢ ($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫ ⦂ ` 0
_ = env (bwf↓ here refl wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$

------------------------------------------------------------------------
-- reveal-only:  B₀ = X→X ;  external ℕ→ℕ, internal X→X.  The reveal's rep ℕ
-- names no blocked slot, so the interior entry is the KNOWLEDGE X:=ℕ.
------------------------------------------------------------------------

_ : intOf [] (rvl `ℕ ∷ []) ≡ rvld `ℕ ∷ []
_ = refl

_ : [] ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ rvl `ℕ ∷ [] , (` 0 ⇒ ` 0) ⟫ ⦂ (`ℕ ⇒ `ℕ)
_ = env (bwf↑ wf-ℕ bwf[]) (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
        (⊢ƛ (wf-var here-rvld) (⊢` here))

------------------------------------------------------------------------
-- THE PARALLEL REVEAL BLOCK (Jeremy's ruling; formerly the telescopic
-- residue (R1)).  Every reveal's rep is read in the PLAIN exterior, so the
-- external face substitutes it as stored — no chain is resolved.  The
-- semantic difference from the reverted telescopic reading, on the boundary
-- ↑Y:=Y′ , ↑Y′:=𝔹 over an exterior that HAS a Y′:
--
--   Θch  =  ↑Y:=Y′ , ↑Y′:=𝔹   over  Δch = Y′:=𝔹
--   parallel:    ρᵇ Θch 0  =  ` 0  =  Y′ THE EXTERIOR VARIABLE
--   telescopic:  ρᵇ Θch 0  would have been  𝔹  (the sibling's rep folded in)
--
-- Under the parallel reading the same boundary over the EMPTY exterior is
-- ill formed (its first rep names a variable that does not exist), which is
-- why the example now carries Δch.
------------------------------------------------------------------------

Δch : TCtx
Δch = rvld `𝔹 ∷ []

Θch : BCtx
Θch = rvl (` 0) ∷ rvl `𝔹 ∷ []

_ : ρᵇ Θch 0 ≡ ` 0                     -- Y ↦ the EXTERIOR Y′, not 𝔹
_ = refl

_ : ρᵇ Θch 1 ≡ `𝔹
_ = refl

-- both entries carry knowledge; Y's is the interior slot of the exterior Y′
_ : intOf Δch Θch ≡ rvld (` 1) ∷ rvld `𝔹 ∷ rvld `𝔹 ∷ []
_ = refl

-- each rep is well formed in the PLAIN exterior — which is what bwf↑ asks for
_ : Δch ∣ intOf Δch Θch ⊢ᵇ Θch
_ = bwf↑ (wf-var here-rvld) (bwf↑ wf-𝔹 bwf[])

-- a value sealed at that boundary:  B₀ = Y→Y, external Y′→Y′
_ : Δch ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ Θch , (` 0 ⇒ ` 0) ⟫ ⦂ (` 0 ⇒ ` 0)
_ = env (bwf↑ (wf-var here-rvld) (bwf↑ wf-𝔹 bwf[]))
        (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
        (⊢ƛ (wf-var here-rvld) (⊢` here))

------------------------------------------------------------------------
-- A REP-LESS ABSTRACT REVEAL.  Its interior entry is `abst`, its baseS slot
-- is `blk`, and its ρᵇ image is a dummy that no Scoped type can reach.
------------------------------------------------------------------------

_ : intOf [] (rvl⋆ ∷ rvl `ℕ ∷ []) ≡ abst ∷ rvld `ℕ ∷ []
_ = refl

_ : baseS (rvl⋆ ∷ rvl `ℕ ∷ []) [] ≡ blk ∷ ok ∷ []
_ = refl

_ : [] ∣ [] ⊢ (ƛ ` 1 ∙ ` 0) ⟪ rvl⋆ ∷ rvl `ℕ ∷ [] , (` 1 ⇒ ` 1) ⟫
        ⦂ (`ℕ ⇒ `ℕ)
_ = env (bwf⋆ (bwf↑ wf-ℕ bwf[]))
        (sc-⇒ (sc-var (thereᵒ hereᵒ)) (sc-var (thereᵒ hereᵒ)))
        (⊢ƛ (wf-var (skip-abst here-rvld)) (⊢` here))

------------------------------------------------------------------------
-- NON-SPURIOUS conceal under a reveal:  same Θ₈ = [↓X(1), ↑Z:=Y], B₀ = X.
--   In the boundary frame Z ∷ Γ₈ = [Z(0), Y(1), X(2)], X sits at index 2
--   (Γ-index 1 lifted past the one reveal).  Both faces are now correct.
------------------------------------------------------------------------

-- external face:  X (bframe idx 2) ↦ ` 1 (= X in Γ₈)
_ : substᵗ (ρᵇ Θ₈) (` 2) ≡ ` 1
_ = refl

-- internal face:  X (bframe idx 2) ↦ ℕ (its rep) — the offset fix resolves it
_ : substᵗ (γᵇ Θ₈) (` 2) ≡ `ℕ
_ = refl

-- and the term types:  ($7)⟪Θ₈, B₀=X⟫ : X   (external ` 1 ;  interior 7 : ℕ)
_ : Γ₈ ∣ [] ⊢ ($ 7) ⟪ Θ₈ , ` 2 ⟫ ⦂ ` 1
_ = env (bwf↓ (skip-abst here) refl wf-ℕ (bwf↑ (wf-var here-abst) bwf[]))
        (sc-var (thereᵒ (thereᵒ hereᵒ))) ⊢$

------------------------------------------------------------------------
-- MULTIPLE concealed variables — the case that grounds the whole-Γ change.
--   Γ = W:=ℕ (0) , X:=ℕ (1) , V:=ℕ (2).   Conceal X (1) and W (0), keeping the
--   DEEPER V (2).  The interior is Γ ↓ (max conceal = 1) = [V].  A value
--   λv:V. 5  (: V→ℕ internally) is sealed to external type V→X.
--
--   Whole-Γ gives interior [V]; the OLD progressive intOf would over-drop
--   (intOf ((Γ↓1)↓0) = []) and V would be out of scope — the example
--   would fail.
--
--   Both conceal reps are CLOSED, so their read-back is themselves and the
--   reversal premise is `refl` against Γ₃'s knowledge.
------------------------------------------------------------------------

Γ₃ : TCtx
Γ₃ = rvld `ℕ ∷ rvld `ℕ ∷ rvld `ℕ ∷ []       -- W(0) , X(1) , V(2)

Θ₃ : BCtx
Θ₃ = cnc 1 `ℕ ∷ cnc 0 `ℕ ∷ []                -- conceal X and W

_ : intOf Γ₃ Θ₃ ≡ rvld `ℕ ∷ []               -- interior = [V], NOT []
_ = refl

-- external V→X (` 2 ⇒ ` 1) ;  interior λv:V.5 : V→ℕ (` 0 ⇒ ℕ)
_ : Γ₃ ∣ [] ⊢ (ƛ ` 0 ∙ $ 5) ⟪ Θ₃ , (` 2 ⇒ ` 1) ⟫ ⦂ (` 2 ⇒ ` 1)
_ = env (bwf↓ (skip-rvld here) refl wf-ℕ (bwf↓ here refl wf-ℕ bwf[]))
        (sc-⇒ (sc-var (thereᵒ (thereᵒ hereᵒ))) (sc-var (thereᵒ hereᵒ)))
        (⊢ƛ (wf-var here-rvld) ⊢$)

------------------------------------------------------------------------
-- THE REVERSAL PREMISE REFUTES THE STUCK VALUES (notes/old/ReversalProbe §1).
--   bad = (7 ⟪ ↓X:=ℕ , X ⟫) ⟪ ↑X:=∀Z.Z→Z , X ⟫ : the inner conceal's rep ℕ
--   reads back out to ℕ, while the exterior knows X = ∀Z.Z→Z.
------------------------------------------------------------------------

∀ZZ : Ty
∀ZZ = `∀ (` 0 ⇒ ` 0)

bad : Term
bad = (($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫) ⟪ rvl ∀ZZ ∷ [] , ` 0 ⟫

-- the outer boundary's interior: X REVEALED at ∀Z.Z→Z
_ : intOf [] (rvl ∀ZZ ∷ []) ≡ rvld ∀ZZ ∷ []
_ = refl

open import Relation.Nullary using (¬_)

¬⊢bad : ¬ ([] ∣ [] ⊢ bad ⦂ ∀ZZ)
¬⊢bad (env _ _ (env (bwf↓ here () _ _) _ _))

-- bad₂ (probe §5): the naive interior comparison accepts it because ` 0 read
-- in Γ↓X and ` 0 read in the interior are different variables; the reversal
-- premise sees the confusion (` 0 reads back out to ℕ, the knowledge is ` 1).
Γb : TCtx
Γb = rvld (` 0) ∷ rvld ∀ZZ ∷ []

Θb : BCtx
Θb = cnc 0 (` 0) ∷ rvl `ℕ ∷ []

_ : outRead Θb (` 0) ≡ `ℕ
_ = refl

_ : upRep 0 (` 0) ≡ ` 1
_ = refl

¬Reversal-bad₂ : ¬ (Reversal Θb 0 (` 0) (` 0))
¬Reversal-bad₂ ()
