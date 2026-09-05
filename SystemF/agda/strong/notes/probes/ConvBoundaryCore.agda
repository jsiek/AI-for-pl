module strong.notes.probes.ConvBoundaryCore where

-- THE CONVERSION-BOUNDARY REDESIGN PROBE — part 1: the SPINE and the FACES.
--
-- This is a self-contained mini-core for the split boundary of
-- notes/RedesignAdvice.md, under Jeremy's rulings:
--
--   * Q1 realization (ii) OWNER-SYNTACTIC: a variable's representation lives
--     ONLY at its owner, which is a context entry (`own A`); every face and
--     every licence resolves the rep by LOOKING THE NAME UP along the
--     enclosing spine (the type context).  There is no store and no copy.
--   * Q3 the faces are GTSF-style CONVERSIONS (id / seal / unseal / ↦ / ∀).
--     Here the two directions of GTSF's mutual pair are ONE judgement indexed
--     by a POLARITY, which is exactly GTSF's ↑ˢ/↓ˢ split (`c-f` flips).
--   * conceal BLOCKS a slot in place (`blk E`, the entry is RETAINED); it
--     never drops it and never re-spells it.  That single change is what
--     deletes the demotion concept: the dual re-points, and the knowledge it
--     re-points to is still sitting in the entry.
--
-- Nothing in this file mentions terms.  Part 2 (ConvBoundaryTerms) adds the
-- boundary and the term typing; part 3 (ConvBoundaryRed) the rules.
--
-- THE TRANSPORT QUESTION (Q1) is settled at this level for conversions:
-- `conv-ren` and `conv-⊑` at the foot of the file.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans; subst)

open import strong.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Var; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)
open import strong.TypeSubst using (rename-cong; rename-rename-commute)

------------------------------------------------------------------------
-- 0.  Two type-renaming facts we need over and over
------------------------------------------------------------------------

-- The single de Bruijn commutation: renaming past one extra binder.
ren-⇑-comm : (ρ : Renameᵗ) (A : Ty)
  → renameᵗ (extᵗ ρ) (⇑ᵗ A) ≡ ⇑ᵗ (renameᵗ ρ A)
ren-⇑-comm ρ A =
  trans (rename-rename-commute suc (extᵗ ρ) A)
        (trans (rename-cong (λ X → refl) A)
               (sym (rename-rename-commute ρ suc A)))

------------------------------------------------------------------------
-- 1.  The spine:  type contexts with OWNER entries and BLOCKED entries
------------------------------------------------------------------------

-- abst    : a Λ-bound variable — no representation, and none can be invented.
-- own A   : THE OWNER of an instantiation event.  A is the representation,
--           stored ONCE, as a type over this entry's own tail.  Every inner
--           boundary that talks about this variable carries only its NAME.
-- blk E   : the slot is CONCEALED here: it may not be NAMED (tightness), but
--           its entry E is RETAINED, so the knowledge is still on the spine
--           for a later re-exposure (`ali`) to point back at.  This is the
--           entry form that replaces the old design's demotion-to-`rvl⋆`.
data Ent : Set where
  abst : Ent
  own  : Ty → Ent
  blk  : Ent → Ent

Ctxᵗ : Set
Ctxᵗ = List Ent

private
  variable
    Δ Δ′ Δ″ : Ctxᵗ
    E E′ F : Ent
    A A′ B B′ C : Ty
    X Y Z : ℕ
    ρ ρ′ : Renameᵗ

renᵉ : Renameᵗ → Ent → Ent
renᵉ ρ abst    = abst
renᵉ ρ (own A) = own (renameᵗ ρ A)
renᵉ ρ (blk E) = blk (renᵉ ρ E)

⇑ᵉ : Ent → Ent
⇑ᵉ = renᵉ suc

renᵉ-⇑-comm : (ρ : Renameᵗ) (E : Ent)
  → renᵉ (extᵗ ρ) (⇑ᵉ E) ≡ ⇑ᵉ (renᵉ ρ E)
renᵉ-⇑-comm ρ abst    = refl
renᵉ-⇑-comm ρ (own A) = cong own (ren-⇑-comm ρ A)
renᵉ-⇑-comm ρ (blk E) = cong blk (renᵉ-⇑-comm ρ E)

-- Slot lookup.  The entry is returned SHIFTED into the ambient context, so
-- `Δ ∋e X , own A` means "slot X is an owner whose rep, read in Δ, is A".
-- One relation serves every purpose: knowledge, visibility, and blocking.
infix 4 _∋e_,_
data _∋e_,_ : Ctxᵗ → ℕ → Ent → Set where
  ez : (E ∷ Δ) ∋e zero , ⇑ᵉ E
  es : Δ ∋e X , E → (F ∷ Δ) ∋e suc X , ⇑ᵉ E

-- A slot may be NAMED iff its entry is not blocked.  This is the whole of
-- the tightness discipline: `blk` is invisible to types and to terms.
data Vis : Ent → Set where
  vis-a : Vis abst
  vis-o : Vis (own A)

renᵉ-Vis : Vis E → Vis (renᵉ ρ E)
renᵉ-Vis vis-a = vis-a
renᵉ-Vis vis-o = vis-o

infix 4 _∋tv_
_∋tv_ : Ctxᵗ → ℕ → Set
Δ ∋tv X = ∃[ E ] ((Δ ∋e X , E) × Vis E)

-- OWNER-SYNTACTIC LOOKUP.  This is the only way any rep is ever read.
infix 4 _∋_:=_
_∋_:=_ : Ctxᵗ → ℕ → Ty → Set
Δ ∋ X := A = Δ ∋e X , own A

∋:=→∋tv : Δ ∋ X := A → Δ ∋tv X
∋:=→∋tv d = own _ , d , vis-o

------------------------------------------------------------------------
-- 2.  Well-formed types over a spine
------------------------------------------------------------------------

infix 4 _⊢ᵗ_
data _⊢ᵗ_ : Ctxᵗ → Ty → Set where
  wf-var : Δ ∋tv X → Δ ⊢ᵗ ` X
  wf-ℕ   : Δ ⊢ᵗ `ℕ
  wf-𝔹   : Δ ⊢ᵗ `𝔹
  wf-⇒   : Δ ⊢ᵗ A → Δ ⊢ᵗ B → Δ ⊢ᵗ (A ⇒ B)
  wf-∀   : (abst ∷ Δ) ⊢ᵗ A → Δ ⊢ᵗ (`∀ A)

data Base : Ty → Set where
  base-ℕ : Base `ℕ
  base-𝔹 : Base `𝔹

base-wf : Base A → Δ ⊢ᵗ A
base-wf base-ℕ = wf-ℕ
base-wf base-𝔹 = wf-𝔹

base-ren : Base A → renameᵗ ρ A ≡ A
base-ren base-ℕ = refl
base-ren base-𝔹 = refl

------------------------------------------------------------------------
-- 3.  Conversions — the FACE half of the boundary (GTSF's grammar)
------------------------------------------------------------------------

-- Rep-free by construction: `csl`/`cus` carry a NAME, never a spelling.
-- `cb`/`cv` are the two identity forms, kept apart so that the
-- ACTIVE/INERT classification is a one-level match on the constructor
-- (see ConvBoundaryRed).
data Conv : Set where
  cb   : Ty → Conv          -- id at a base type          ACTIVE
  cv   : ℕ → Conv           -- id at a type variable      INERT
  csl  : ℕ → Conv           -- seal   at the owner named  INERT
  cus  : ℕ → Conv           -- unseal at the owner named  ACTIVE
  _⇛_  : Conv → Conv → Conv -- s ↦ t, contravariant dom   INERT
  ∀ᶜ_  : Conv → Conv        -- ∀ s                        INERT

infixr 7 _⇛_
infix 6 ∀ᶜ_

renᶜ : Renameᵗ → Conv → Conv
renᶜ ρ (cb A)  = cb (renameᵗ ρ A)
renᶜ ρ (cv X)  = cv (ρ X)
renᶜ ρ (csl X) = csl (ρ X)
renᶜ ρ (cus X) = cus (ρ X)
renᶜ ρ (s ⇛ t) = renᶜ ρ s ⇛ renᶜ ρ t
renᶜ ρ (∀ᶜ s)  = ∀ᶜ (renᶜ (extᵗ ρ) s)

-- Polarity.  GTSF's two mutually defined judgements ↑ˢ / ↓ˢ, merged into one
-- indexed family: `+` unseals at positive positions (a REVEAL face), `-`
-- seals at positive positions (a CONCEAL face), and `c-f` flips on domains.
data Pol : Set where
  pos neg : Pol

flip : Pol → Pol
flip pos = neg
flip neg = pos

flip-flip : (p : Pol) → flip (flip p) ≡ p
flip-flip pos = refl
flip-flip neg = refl

-- Δ ⊢ c ∶ A ⇝ B ∙ p   —   c converts the INTERIOR face A to the EXTERIOR
-- face B, both read on the spine Δ (the FACE CONTEXT: the spine at which the
-- boundary's owners are live).  Every rep is read by NAME from Δ.
infix 4 _⊢_∶_⇝_∙_
data _⊢_∶_⇝_∙_ : Ctxᵗ → Conv → Ty → Ty → Pol → Set where

  c-b : ∀ {p} → Base A
        --------------------------------
      → Δ ⊢ cb A ∶ A ⇝ A ∙ p

  c-v : ∀ {p} → Δ ∋tv X
        --------------------------------
      → Δ ⊢ cv X ∶ ` X ⇝ ` X ∙ p

  -- REVEAL: the interior sees the abstract name, the exterior its rep.
  c-u : Δ ∋ X := A
        --------------------------------
      → Δ ⊢ cus X ∶ ` X ⇝ A ∙ pos

  -- CONCEAL: the interior sees the rep, the exterior the abstract name.
  -- THE SOUNDNESS GATE (Q3): a seal must cite a LIVE OWNER on its spine.
  c-s : Δ ∋ X := A
        --------------------------------
      → Δ ⊢ csl X ∶ A ⇝ ` X ∙ neg

  c-f : ∀ {p s t} → Δ ⊢ s ∶ A′ ⇝ A ∙ flip p → Δ ⊢ t ∶ B ⇝ B′ ∙ p
        ----------------------------------------------------------
      → Δ ⊢ s ⇛ t ∶ (A ⇒ B) ⇝ (A′ ⇒ B′) ∙ p

  c-a : ∀ {p s} → (abst ∷ Δ) ⊢ s ∶ A ⇝ B ∙ p
        --------------------------------------
      → Δ ⊢ ∀ᶜ s ∶ `∀ A ⇝ `∀ B ∙ p

------------------------------------------------------------------------
-- 4.  The identity conversion at an arbitrary type
------------------------------------------------------------------------

idc : Ty → Conv
idc (` X)   = cv X
idc `ℕ      = cb `ℕ
idc `𝔹      = cb `𝔹
idc (A ⇒ B) = idc A ⇛ idc B
idc (`∀ A)  = ∀ᶜ (idc A)

idc-⊢ : ∀ {p} → Δ ⊢ᵗ A → Δ ⊢ idc A ∶ A ⇝ A ∙ p
idc-⊢ (wf-var tv)  = c-v tv
idc-⊢ wf-ℕ         = c-b base-ℕ
idc-⊢ wf-𝔹         = c-b base-𝔹
idc-⊢ (wf-⇒ wA wB) = c-f (idc-⊢ wA) (idc-⊢ wB)
idc-⊢ (wf-∀ wA)    = c-a (idc-⊢ wA)

------------------------------------------------------------------------
-- 5.  TRANSPORT I — spine renaming  (the ⊢renameᵀ analog)
------------------------------------------------------------------------

-- A renaming of spines.  ONE field: it moves the ENTRY at every slot,
-- blocked entries included.  Knowledge transport (`ren-kn` below) is then
-- DEFINITIONAL — which is the whole bet of the ownership design: a name is
-- moved by ρ, a spelling would have had to be re-derived.
record Ren (ρ : Renameᵗ) (Δ Δ′ : Ctxᵗ) : Set where
  constructor mkRen
  field ren∋ : ∀ {X E} → Δ ∋e X , E → Δ′ ∋e ρ X , renᵉ ρ E

open Ren public

ren-kn : Ren ρ Δ Δ′ → Δ ∋ X := A → Δ′ ∋ ρ X := renameᵗ ρ A
ren-kn r d = ren∋ r d

ren-tv : Ren ρ Δ Δ′ → Δ ∋tv X → Δ′ ∋tv ρ X
ren-tv r (E , d , v) = renᵉ _ E , ren∋ r d , renᵉ-Vis v

ren-ext : Ren ρ Δ Δ′ → Ren (extᵗ ρ) (F ∷ Δ) (renᵉ ρ F ∷ Δ′)
ren-ext {ρ = ρ} {Δ = Δ} {Δ′ = Δ′} {F = F} r = mkRen go
  where
  go : ∀ {X E} → (F ∷ Δ) ∋e X , E
     → (renᵉ ρ F ∷ Δ′) ∋e extᵗ ρ X , renᵉ (extᵗ ρ) E
  go ez     rewrite renᵉ-⇑-comm ρ F = ez
  go (es {E = E₀} d) rewrite renᵉ-⇑-comm ρ E₀ = es (ren∋ r d)

-- Well-formed types transport.
wf-ren : Ren ρ Δ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ renameᵗ ρ A
wf-ren r (wf-var tv)  = wf-var (ren-tv r tv)
wf-ren r wf-ℕ         = wf-ℕ
wf-ren r wf-𝔹         = wf-𝔹
wf-ren r (wf-⇒ wA wB) = wf-⇒ (wf-ren r wA) (wf-ren r wB)
wf-ren r (wf-∀ wA)    = wf-∀ (wf-ren (ren-ext r) wA)

-- THE FIRST HALF OF Q1.  A spine-indexed conversion typing moves along ANY
-- spine renaming, with NO hypothesis beyond `Ren` itself: no SkelEq, no
-- starOnly, no unfolding, no second chance.  The `c-u`/`c-s` cases are
-- literally `ren-kn` — the name is carried, and the rep comes back out of
-- the target spine already renamed.
conv-ren : ∀ {p c} → Ren ρ Δ Δ′
  → Δ  ⊢ c ∶ A ⇝ B ∙ p
    -----------------------------------------------------------
  → Δ′ ⊢ renᶜ ρ c ∶ renameᵗ ρ A ⇝ renameᵗ ρ B ∙ p
conv-ren {ρ = ρ} r (c-b bA) rewrite base-ren {A = _} {ρ = ρ} bA = c-b bA
conv-ren r (c-v tv)  = c-v (ren-tv r tv)
conv-ren r (c-u d)   = c-u (ren-kn r d)
conv-ren r (c-s d)   = c-s (ren-kn r d)
conv-ren r (c-f s t) = c-f (conv-ren r s) (conv-ren r t)
conv-ren r (c-a s)   = c-a (conv-ren (ren-ext r) s)

------------------------------------------------------------------------
-- 6.  TRANSPORT II — spine growth / knowledge refinement (the ⊢retag analog)
------------------------------------------------------------------------

-- E ⊑ᵉ E′ : E′ knows at least what E knows.
--   le-ao : a Λ-bound slot may become an owner              (TyBeta)
--   le-bu : a concealed slot may be re-exposed              (Cancel)
--   le-bb : concealment is monotone in what it hides
-- There is NO clause in the other direction: an owner never loses its rep.
-- The old design's demotion (rvld ↦ abst via rvl⋆) is not expressible here.
data _⊑ᵉ_ : Ent → Ent → Set where
  le-aa : abst ⊑ᵉ abst
  le-ao : abst ⊑ᵉ own A
  le-oo : own A ⊑ᵉ own A
  le-bb : E ⊑ᵉ E′ → blk E ⊑ᵉ blk E′
  le-bu : E ⊑ᵉ E′ → Vis E′ → blk E ⊑ᵉ E′

infix 4 _⊑_
data _⊑_ : Ctxᵗ → Ctxᵗ → Set where
  le[] : [] ⊑ []
  le∷  : E ⊑ᵉ E′ → Δ ⊑ Δ′ → (E ∷ Δ) ⊑ (E′ ∷ Δ′)

⊑ᵉ-refl : (E : Ent) → E ⊑ᵉ E
⊑ᵉ-refl abst    = le-aa
⊑ᵉ-refl (own A) = le-oo
⊑ᵉ-refl (blk E) = le-bb (⊑ᵉ-refl E)

⊑-refl : (Δ : Ctxᵗ) → Δ ⊑ Δ
⊑-refl []      = le[]
⊑-refl (E ∷ Δ) = le∷ (⊑ᵉ-refl E) (⊑-refl Δ)

⊑ᵉ-⇑ : E ⊑ᵉ E′ → ⇑ᵉ E ⊑ᵉ ⇑ᵉ E′
⊑ᵉ-⇑ le-aa        = le-aa
⊑ᵉ-⇑ le-ao        = le-ao
⊑ᵉ-⇑ le-oo        = le-oo
⊑ᵉ-⇑ (le-bb l)    = le-bb (⊑ᵉ-⇑ l)
⊑ᵉ-⇑ (le-bu l v)  = le-bu (⊑ᵉ-⇑ l) (renᵉ-Vis v)

⊑-∋e : Δ ⊑ Δ′ → Δ ∋e X , E → ∃[ E′ ] ((Δ′ ∋e X , E′) × E ⊑ᵉ E′)
⊑-∋e (le∷ l ls) ez     = _ , ez , ⊑ᵉ-⇑ l
⊑-∋e (le∷ l ls) (es d) with ⊑-∋e ls d
... | E′ , d′ , l′ = _ , es d′ , ⊑ᵉ-⇑ l′

⊑-tv : Δ ⊑ Δ′ → Δ ∋tv X → Δ′ ∋tv X
⊑-tv ls (E , d , v) with ⊑-∋e ls d
... | E′ , d′ , l′ = E′ , d′ , vis-mono l′ v
  where
  vis-mono : ∀ {E E′} → E ⊑ᵉ E′ → Vis E → Vis E′
  vis-mono le-aa        vis-a = vis-a
  vis-mono le-ao        vis-a = vis-o
  vis-mono le-oo        vis-o = vis-o
  vis-mono (le-bb _)    ()
  vis-mono (le-bu _ _)  ()

-- An owner is never lost and never re-spelled: the ONLY ⊑ᵉ clause whose
-- source is `own A` is `le-oo`.  This is the deleted demotion, as a theorem.
⊑-kn : Δ ⊑ Δ′ → Δ ∋ X := A → Δ′ ∋ X := A
⊑-kn ls d with ⊑-∋e ls d
... | own A , d′ , le-oo = d′

⊑-wf : Δ ⊑ Δ′ → Δ ⊢ᵗ A → Δ′ ⊢ᵗ A
⊑-wf ls (wf-var tv)  = wf-var (⊑-tv ls tv)
⊑-wf ls wf-ℕ         = wf-ℕ
⊑-wf ls wf-𝔹         = wf-𝔹
⊑-wf ls (wf-⇒ wA wB) = wf-⇒ (⊑-wf ls wA) (⊑-wf ls wB)
⊑-wf ls (wf-∀ wA)    = wf-∀ (⊑-wf (le∷ le-aa ls) wA)

-- THE SECOND HALF OF Q1.  Knowledge refinement preserves conversion typing
-- with the FACES UNCHANGED — no ≈, no unfolding, no retagging of the types.
conv-⊑ : ∀ {p c} → Δ ⊑ Δ′
  → Δ  ⊢ c ∶ A ⇝ B ∙ p
    ------------------------
  → Δ′ ⊢ c ∶ A ⇝ B ∙ p
conv-⊑ ls (c-b bA)  = c-b bA
conv-⊑ ls (c-v tv)  = c-v (⊑-tv ls tv)
conv-⊑ ls (c-u d)   = c-u (⊑-kn ls d)
conv-⊑ ls (c-s d)   = c-s (⊑-kn ls d)
conv-⊑ ls (c-f s t) = c-f (conv-⊑ ls s) (conv-⊑ ls t)
conv-⊑ ls (c-a s)   = c-a (conv-⊑ (le∷ le-aa ls) s)
