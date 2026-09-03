module strong.Boundary where

-- Tight, dual boundary — typing, on the BOUNDARY-TYPE (B₀) formulation.
--
--   reveal  X:=A :  X fresh INTERNAL var;  A (rep) EXTERNAL to the whole boundary.
--   conceal Y:=A :  Y EXTERNAL var;         A (rep) INTERNAL to the whole boundary.
--
-- TIGHT: a conceal restricts the interior to Y's existential scope (Γ ↓ Y); a
-- reveal adds a fresh abstract var.  A wrapper  M ⟪ Θ , B₀ ⟫  records the BOUNDARY
-- type B₀; the internal and external types are its two projections:
--
--   internal = substᵗ (γᵇ Θ) B₀       -- conceals resolved to their reps
--   external = substᵗ (ρᵇ Θ) B₀       -- reveals  resolved to their reps
--
-- so there is NO consistency premise — both faces come from one B₀ (the (env)
-- rule we chose, not the looser τ(A)=σ(B) form).

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_)
open import Data.Nat.Properties using (_≟_)
open import Data.Nat using (_<?_; _≤?_)
open import Data.Bool using (Bool; true; false; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Nullary using (yes; no; ⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import strong.Types
open import strong.TypeSubst using (_⨟ᵗ_)
open import strong.Context
  using (TCtx; abst; rvld; _↓_; _⊢_; wf-var; wf-ℕ; wf-𝔹; wf-⇒; wf-∀;
         _∋tv_; here-abst; here-rvld; skip-abst; skip-rvld;
         Ctx; _∋_⦂_; here; there; ⤊)

------------------------------------------------------------------------
-- Boundary
------------------------------------------------------------------------

data BEntry : Set where
  rvl : Ty → BEntry       -- reveal a fresh internal var;  A = external rep
  cnc : ℕ → Ty → BEntry   -- conceal external var at index X;  A = internal rep

BCtx : Set
BCtx = List BEntry

-- Conceal indices are WHOLE-Γ relative: the interior is everything DEEPER than
-- the deepest conceal (Γ ↓ cmax), with the reveal variables prepended.  This
-- "whole-Γ" projection keeps conceal indices uniform (no progressive shifting),
-- which is what makes renaming/substitution tractable.

revs : BCtx → ℕ                 -- number of reveals
revs []             = 0
revs (rvl A   ∷ Θ) = suc (revs Θ)
revs (cnc X A ∷ Θ) = revs Θ

cmax : BCtx → ℕ                 -- 1 + (max conceal index), 0 if no conceals
cmax []             = 0
cmax (rvl A   ∷ Θ) = cmax Θ
cmax (cnc X A ∷ Θ) = suc X ⊔ cmax Θ

dropN : ℕ → TCtx → TCtx         -- drop the first n (shallowest) entries
dropN zero    Γ       = Γ
dropN (suc n) []      = []
dropN (suc n) (E ∷ Γ) = dropN n Γ

prepAbst : ℕ → TCtx → TCtx      -- prepend n fresh abstract variables
prepAbst zero    Γ = Γ
prepAbst (suc n) Γ = abst ∷ prepAbst n Γ

-- interior context: reveals prepended, everything up to the deepest conceal dropped
intOf : TCtx → BCtx → TCtx
intOf Γ Θ = prepAbst (revs Θ) (dropN (cmax Θ) Γ)

-- ρᵇ : reveal-resolve.  Reveal var ↦ its rep; the exterior passes through (shifted
-- below the reveal vars).  Conceals leave the exterior unchanged.  B₀ ↦ external.
ρᵇ : BCtx → Substᵗ
ρᵇ []             = `_
ρᵇ (rvl A   ∷ Θ) = A •ᵗ ρᵇ Θ
ρᵇ (cnc X A ∷ Θ) = ρᵇ Θ

-- γᵇ : conceal-resolve, on the boundary frame (reveals ++ Γ, reveals shallow).
-- A reveal var (bframe index < revs) passes through unchanged.  For a Γ-index i:
-- a concealed index ↦ its rep (already over the WHOLE interior — NOT shifted, so a
-- rep may mention a reveal var), a DEEPER (kept) index ↦ its interior slot
-- ` (revs + (i ∸ cmax)).
sover : ℕ → Ty → Substᵗ → Substᵗ    -- override index X with A, else σ
sover X A σ Y with X ≟ Y
... | yes _ = A
... | no  _ = σ Y

γcnc : ℕ → ℕ → BCtx → Substᵗ        -- r=revs, m=cmax : resolve a Γ-index i
γcnc r m []             = λ i → ` (r + (i ∸ m))
γcnc r m (rvl A   ∷ Θ) = γcnc r m Θ
γcnc r m (cnc X A ∷ Θ) = sover X A (γcnc r m Θ)

prepId : ℕ → Substᵗ → Substᵗ        -- first r indices identity, NO output shift
prepId r σ j with j <? r
... | yes _ = ` j
... | no  _ = σ (j ∸ r)

γᵇ : BCtx → Substᵗ
γᵇ Θ = prepId (revs Θ) (γcnc (revs Θ) (cmax Θ) Θ)

------------------------------------------------------------------------
-- Boundary-type scope.  A "blocked" bframe slot — a Γ-index shallower than cmax
-- that is not itself concealed — has NO interior image; γᵇ would silently alias
-- it onto a kept var.  The (env) rule forbids B₀ from naming a blocked slot: it
-- must be Scoped over the accessibility stack, in which blocked slots are `blk`.
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
isConc i []             = false
isConc i (rvl _   ∷ Θ) = isConc i Θ
isConc i (cnc X _ ∷ Θ) = ⌊ i ≟ X ⌋ ∨ isConc i Θ

slotAt : BCtx → ℕ → Slot             -- Γ-index i : kept (≥cmax) or concealed → ok
slotAt Θ i with cmax Θ ≤? i
... | yes _ = ok
... | no  _ = if isConc i Θ then ok else blk

slotsᴳ : BCtx → ℕ → TCtx → SCtx      -- slots for Γ from index i onward
slotsᴳ Θ i []      = []
slotsᴳ Θ i (_ ∷ Γ) = slotAt Θ i ∷ slotsᴳ Θ (suc i) Γ

repl-ok : ℕ → SCtx                   -- the reveal prefix: all accessible
repl-ok zero    = []
repl-ok (suc r) = ok ∷ repl-ok r

baseS : BCtx → TCtx → SCtx           -- accessibility stack for B₀ over the bframe
baseS Θ Γ = repl-ok (revs Θ) ++ slotsᴳ Θ 0 Γ

-- scope-restricted subst-cong: two substitutions agreeing on the accessible slots
-- act the same on a Scoped type (blocked slots are irrelevant).
subst-cong-sc : ∀ {Ψ}{σ τ : Substᵗ} {A}
  → Scoped Ψ A → (∀ X → Ψ ∋ok X → σ X ≡ τ X) → substᵗ σ A ≡ substᵗ τ A
subst-cong-sc (sc-var p) h = h _ p
subst-cong-sc sc-ℕ h = refl
subst-cong-sc sc-𝔹 h = refl
subst-cong-sc (sc-⇒ sA sB) h = cong₂ _⇒_ (subst-cong-sc sA h) (subst-cong-sc sB h)
subst-cong-sc {Ψ}{σ}{τ} (sc-∀ sA) h = cong `∀ (subst-cong-sc sA h-ext)
  where
    h-ext : ∀ X → (ok ∷ Ψ) ∋ok X → extsᵗ σ X ≡ extsᵗ τ X
    h-ext zero    hereᵒ      = refl
    h-ext (suc X) (thereᵒ p) = cong (renameᵗ suc) (h X p)

------------------------------------------------------------------------
-- Boundary well-formedness.  Reveal rep read in the exterior Γ; conceal rep in
-- the interior Ψ (= intOf Γ Θ).
------------------------------------------------------------------------

data _∣_⊢ᵇ_ : TCtx → TCtx → BCtx → Set where
  bwf[] : ∀ {Γ Ψ}       →                                  Γ ∣ Ψ ⊢ᵇ []
  bwf↑  : ∀ {Γ Ψ A Θ}   → Γ ⊢ A            → Γ ∣ Ψ ⊢ᵇ Θ →  Γ ∣ Ψ ⊢ᵇ (rvl A ∷ Θ)
  bwf↓  : ∀ {Γ Ψ X A Θ} → Γ ∋tv X → Ψ ⊢ A  → Γ ∣ Ψ ⊢ᵇ Θ →  Γ ∣ Ψ ⊢ᵇ (cnc X A ∷ Θ)

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
  -- B₀ must be Scoped over the accessibility stack (no reference to a blocked slot).
  env : Δ ∣ intOf Δ Θ ⊢ᵇ Θ
      → Scoped (baseS Θ Δ) B₀
      → intOf Δ Θ ∣ [] ⊢ M ⦂ substᵗ (γᵇ Θ) B₀
        ---------------------------------------------------
      → Δ ∣ Γₜ ⊢ M ⟪ Θ , B₀ ⟫ ⦂ substᵗ (ρᵇ Θ) B₀

------------------------------------------------------------------------
-- Example 8 (spurious conceal):  B₀ = Z→Z ;  internal Z→Z, external Y→Y
------------------------------------------------------------------------

Γ₈ : TCtx
Γ₈ = abst ∷ rvld `ℕ ∷ []

Θ₈ : BCtx
Θ₈ = cnc 1 `ℕ ∷ rvl (` 0) ∷ []

_ : intOf Γ₈ Θ₈ ≡ abst ∷ []
_ = refl

_ : Γ₈ ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ Θ₈ , (` 0 ⇒ ` 0) ⟫ ⦂ (` 0 ⇒ ` 0)
_ = env (bwf↓ (skip-abst here-rvld) wf-ℕ (bwf↑ (wf-var here-abst) bwf[]))
        (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
        (⊢ƛ (wf-var here-abst) (⊢` here))

------------------------------------------------------------------------
-- Example 1 (NON-spurious conceal):  B₀ = X ;  external X, internal ℕ
------------------------------------------------------------------------

_ : (rvld `ℕ ∷ []) ∣ [] ⊢ ($ 7) ⟪ cnc 0 `ℕ ∷ [] , ` 0 ⟫ ⦂ ` 0
_ = env (bwf↓ here-rvld wf-ℕ bwf[]) (sc-var hereᵒ) ⊢$

------------------------------------------------------------------------
-- reveal-only:  B₀ = X→X ;  external ℕ→ℕ, internal X→X
------------------------------------------------------------------------

_ : [] ∣ [] ⊢ (ƛ ` 0 ∙ ` 0) ⟪ rvl `ℕ ∷ [] , (` 0 ⇒ ` 0) ⟫ ⦂ (`ℕ ⇒ `ℕ)
_ = env (bwf↑ wf-ℕ bwf[]) (sc-⇒ (sc-var hereᵒ) (sc-var hereᵒ))
        (⊢ƛ (wf-var here-abst) (⊢` here))

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
_ = env (bwf↓ (skip-abst here-rvld) wf-ℕ (bwf↑ (wf-var here-abst) bwf[]))
        (sc-var (thereᵒ (thereᵒ hereᵒ))) ⊢$

------------------------------------------------------------------------
-- MULTIPLE concealed variables — the case that grounds the whole-Γ change.
--   Γ = W:=ℕ (0) , X:=ℕ (1) , V:=ℕ (2).   Conceal X (1) and W (0), keeping the
--   DEEPER V (2).  The interior is Γ ↓ (max conceal = 1) = [V].  A value
--   λv:V. 5  (: V→ℕ internally) is sealed to external type V→X.
--
--   Whole-Γ gives interior [V]; the OLD progressive intOf would over-drop
--   (intOf ((Γ↓1)↓0) = []) and V would be out of scope — the example would fail.
------------------------------------------------------------------------

Γ₃ : TCtx
Γ₃ = rvld `ℕ ∷ rvld `ℕ ∷ rvld `ℕ ∷ []       -- W(0) , X(1) , V(2)

Θ₃ : BCtx
Θ₃ = cnc 1 `ℕ ∷ cnc 0 `ℕ ∷ []                -- conceal X and W

_ : intOf Γ₃ Θ₃ ≡ rvld `ℕ ∷ []               -- interior = [V], NOT []
_ = refl

-- external V→X (` 2 ⇒ ` 1) ;  interior λv:V.5 : V→ℕ (` 0 ⇒ ℕ)
_ : Γ₃ ∣ [] ⊢ (ƛ ` 0 ∙ $ 5) ⟪ Θ₃ , (` 2 ⇒ ` 1) ⟫ ⦂ (` 2 ⇒ ` 1)
_ = env (bwf↓ (skip-rvld here-rvld) wf-ℕ (bwf↓ here-rvld wf-ℕ bwf[]))
        (sc-⇒ (sc-var (thereᵒ (thereᵒ hereᵒ))) (sc-var (thereᵒ hereᵒ)))
        (⊢ƛ (wf-var here-rvld) ⊢$)
