module ImprecisionWorld where

-- File Charter:
--   * THE WORLDS OF CAST-TERM IMPRECISION (GTNF/design.md §12.2; D11-D16).
--     §1 order-preserving embeddings of name positions `_↪_` (GTSFImp's
--     `_↪ᵗ_` with `keep`/`skip`, here indexed by the name list and the
--     center) and their renaming `emb`; §2 the rep. var correspondence
--     `RepRel` and its renumberings; §3 `World` and `Paired` (ϱ = ϱᵍ ∪
--     ϱˡ); §4 type imprecision at a world `_⊑ᵂ⟨_⟩_`; §5 the world
--     operations `W ⊕ m`, `W ⊕ᴸ`, `W ⊕ᴿ m`, `W ⊕⁺ m ^ β`, the
--     allocation renumberings, and `underν²`; §6 the term-interior
--     world `Interior W Θ Θ′ Wᵢ` and conversion-context world
--     `ConversionInterior W Θ Θ′ Wᶜ`, both RELATIONS; §7 term-context
--     imprecision `CtxImp`; §8 well-formedness `WfWorld`, a SEPARATE
--     predicate, with payload imprecision `RepImp` (D23) and named
--     uniqueness `NamedUniqueᴸ`/`NamedUniqueᴿ` (D25).
--   * ϱ IS ANY RELATION WHOSE PAIRS AGREE (design.md D25, revising
--     D13's "a right rep. var has at most one left partner").  What
--     the rejoin of `Interior` needs instead is NAMED UNIQUENESS: among
--     the rep. vars named on one side, at most one is paired with a
--     given rep. var named on the other.  It is the weakest condition
--     of this form that keeps `Interior` usable: a fresh name must
--     join every other-side name of a paired rep. var, and an
--     embedding joins it to at most one, so without it no interior
--     world exists (both directions: fresh names arise on either
--     side).  Unnamed rep. vars are free, which admits C12 (one left
--     rep. var, several right partners, one named at a time) and L3d
--     (one right rep. var, two left partners, store rep. vars with no
--     name); allocations never name a rep. var, so every evolution
--     step preserves it.  Stated over rep. vars, not positions:
--     coherence (`WfCtx.name-fn`) makes names injective on rep. vars.
--   * DEFINITIONS ONLY.  Model: GTSFImp/proof/DGG/CtxImp.agda (`World`,
--     `ηᴸʷ`/`ηᴿʷ`, `impEnvʷ`, `_⊑ᵂ⟨_⟩_`, `CtxImp`), minus the stores,
--     `RebaseAt` and `ImpEnvMono` (no part of a world is ever rebased,
--     design.md §12.2; marks are chosen at the binder, D11).
--   * REPRESENTATION CHOICES.
--     - A world is indexed by the two type contexts `Δ` (left, more
--       precise) and `Δ′` (right).
--     - THE CENTER Ω IS THE MARK LIST `μʷ`: one center name per entry,
--       with its mark (index 0 at the head).  So `μ : ImpEnv(Ω)` and Ω
--       are one field, and a center name is a position in `μʷ`.
--     - The embeddings are indexed by `names Δ` and by `μʷ`, so they
--       cover every name in scope by construction.  `emb` is the
--       identity past the end (only in-range positions are ever read).
--     - ϱ is two lists of pairs (left rep. var, right rep. var) over the
--       CURRENT de Bruijn rep. vars of the two sides: `ϱᵍʷ` (global,
--       store rep. vars) and `ϱˡʷ` (lexical, rep. vars bound by an
--       enclosing Λ, or by the right boundary `∀⊑⟪+⟫` reads).  A binder
--       or an allocation renumbers the side it acts on.
--     - `Interior` is declarative.  A continuing name (one `toExt` sends
--       to an exterior position) keeps its center partner and its mark;
--       a name the boundary itself introduces (`Fresh`) joins the other
--       side's name exactly when their rep. vars are paired by ϱ (D25:
--       a right `+X^β` rejoins the left partner of β whose name is in
--       scope; ϱ may give β several partners, named uniqueness in
--       `WfWorld` keeps the rejoin unique); fresh marks are
--       unconstrained, so the derivation chooses them (D11).  Nothing
--       is said about the worlds between the entries (D15).
--   * PAYLOADS ARE COMPARED IN THE REPRESENTATION UNIVERSE (design.md
--     D23; Jeremy, 2026-10-03).  `Agree.rep-rep` relates two payloads
--     by `RepImp` (§8, `μ ⊢ R ⊑ᴿ⟨ W ⟩ R′`): free rep. vars correspond
--     through `Paired W`, local ∀-bound variables position-wise with
--     marks.  This replaces the earlier deviation that read payloads
--     as ordinary types through each side's names, which failed for a
--     payload mentioning a rep. var hidden by a boundary
--     (proof/DGG/drafts/EvolveImpWfInteriorCounterexample.agda).
--   * DEVIATIONS from design.md §12.2 (each also in the report):
--     - `Interior` does not require `WfWorld Wᵢ`, although §12.2 says
--       W[δ ∥ δ′] "is defined only when it is well formed": WfWorld is
--       kept separate (only the final world Wᵢ would be constrained,
--       D15), and the rules read only the joins and marks fixed here.
--     - `W ⊕⁺ m ^ β` (the premise world of `∀⊑⟪+⟫`) is its own
--       operation: the right side's new name is the boundary entry
--       `bind 0 β`, not a Λ, so the right context is `reps Δ′ ∣ β ∷
--       names Δ′`, not `underΛ Δ′`; the lexical pair is (0, β).
--     - `ConversionInterior`, like `Interior`, does not require
--       `WfWorld Wᶜ`.  A conversion context is the union of names live
--       anywhere along a boundary, so continuation/freshness is stated
--       by whether the name's rep. var already has an exterior name,
--       rather than by `toExt` on the term-interior context.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (_+_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
  using (Ty; `_; ★; _⇒_; `∀; Base; Renameᵗ; renameᵗ; ⇑ᵗ)
open import Ctx
open import Boundary using (Boundary; _⊢ⁱ_⇒_; _⊢ᶜ_⇒_; toExt; Fresh)
open import Imprecision
  using (VarImp; X⊑X; X⊑★; ImpEnv; extᵐ; instᵐ; _⊢_⊑_)
open import Coercion using (NonVar; NonStar; _∈ᵗ_)

private
  variable
    Δ Δ′ Δᵢ Δ′ᵢ Δᶜ Δ′ᶜ : Ctxᵗ

------------------------------------------------------------------------
-- 1. Embeddings of name positions into the center
------------------------------------------------------------------------

-- `η : names Δ ↪ Ω`: an order-preserving embedding of Δ's name
-- positions into the center Ω (GTSFImp `_↪ᵗ_`).  `keep` sends the
-- next name to the next center name; `skip` passes a center name this
-- side does not see.
infix 4 _↪_
data _↪_ : TyCtx → ImpEnv → Set where
  []↪  : [] ↪ []
  keep : ∀ {α m Δ Ω} → Δ ↪ Ω → (α ∷ Δ) ↪ (m ∷ Ω)
  skip : ∀ {m Δ Ω} → Δ ↪ Ω → Δ ↪ (m ∷ Ω)

-- its renaming (GTSFImp `toRenameᵗ`)
emb : ∀ {η Ω} → η ↪ Ω → Renameᵗ
emb []↪      X       = X
emb (keep ι) zero    = zero
emb (keep ι) (suc X) = suc (emb ι X)
emb (skip ι) X       = suc (emb ι X)

-- a renumbering of the rep. vars the names denote moves no position
relabel : ∀ {η Ω} (f : RVar → RVar) → η ↪ Ω → map f η ↪ Ω
relabel f []↪      = []↪
relabel f (keep ι) = keep (relabel f ι)
relabel f (skip ι) = skip (relabel f ι)

------------------------------------------------------------------------
-- 2. The rep. var correspondence
------------------------------------------------------------------------

-- pairs (left rep. var, right rep. var)
RepRel : Set
RepRel = List (RVar × RVar)

infix 4 _∋ᵨ_⇔_
data _∋ᵨ_⇔_ : RepRel → RVar → RVar → Set where
  here⇔  : ∀ {ϱ α β} → ((α , β) ∷ ϱ) ∋ᵨ α ⇔ β
  there⇔ : ∀ {ϱ α β π} → ϱ ∋ᵨ α ⇔ β → (π ∷ ϱ) ∋ᵨ α ⇔ β

sucᴸ sucᴿ suc² : RVar × RVar → RVar × RVar
sucᴸ (α , β) = suc α , β
sucᴿ (α , β) = α , suc β
suc² (α , β) = suc α , suc β

-- one new rep. var on the left, on the right, on both sides
shiftᴸ shiftᴿ shift² : RepRel → RepRel
shiftᴸ = map sucᴸ
shiftᴿ = map sucᴿ
shift² = map suc²

------------------------------------------------------------------------
-- 3. Worlds
------------------------------------------------------------------------

record World (Δ Δ′ : Ctxᵗ) : Set where
  constructor world
  field
    μʷ  : ImpEnv                -- the center Ω, each name with its mark
    ηᴸʷ : names Δ ↪ μʷ          -- the left names
    ηᴿʷ : names Δ′ ↪ μʷ         -- the right names
    ϱᵍʷ : RepRel                -- global: store rep. vars (D16)
    ϱˡʷ : RepRel                -- lexical: Λ- and boundary-bound (D16)
open World public

-- ϱ = ϱᵍ ∪ ϱˡ
Paired : World Δ Δ′ → RVar → RVar → Set
Paired W α β = (ϱᵍʷ W ∋ᵨ α ⇔ β) ⊎ (ϱˡʷ W ∋ᵨ α ⇔ β)

-- a left and a right position name the same center name
Joins : World Δ Δ′ → ℕ → ℕ → Set
Joins W X X′ = emb (ηᴸʷ W) X ≡ emb (ηᴿʷ W) X′

-- the closed world: no names, no rep. vars paired
∅ʷ : World empty empty
∅ʷ = world [] []↪ []↪ [] []

------------------------------------------------------------------------
-- 4. Type imprecision at a world (GTSFImp `_⊑ᵂ⟨_⟩_`)
------------------------------------------------------------------------

embᴸ : World Δ Δ′ → Ty → Ty
embᴸ W = renameᵗ (emb (ηᴸʷ W))

embᴿ : World Δ Δ′ → Ty → Ty
embᴿ W = renameᵗ (emb (ηᴿʷ W))

infix 4 _⊑ᵂ⟨_⟩_
_⊑ᵂ⟨_⟩_ : Ty → World Δ Δ′ → Ty → Set
A ⊑ᵂ⟨ W ⟩ A′ = μʷ W ⊢ embᴸ W A ⊑ embᴿ W A′

------------------------------------------------------------------------
-- 5. World operations (design.md §12.2)
------------------------------------------------------------------------

-- W ⊕ X:m — both sides bind X by a Λ: a new center name in both
-- images with mark m, and the two abstract rep. vars paired lexically
infixl 6 _⊕_ _⊕ᴿ_
_⊕_ : World Δ Δ′ → VarImp → World (underΛ Δ) (underΛ Δ′)
world μ η η′ ϱᵍ ϱˡ ⊕ m =
  world (m ∷ μ) (keep (relabel suc η)) (keep (relabel suc η′))
        (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ)

-- W ⊕ᴸ X — the left side alone binds X: in η's image only, at X⊑★;
-- its abstract rep. var is unpaired
infixl 6 _⊕ᴸ
_⊕ᴸ : World Δ Δ′ → World (underΛ Δ) Δ′
world μ η η′ ϱᵍ ϱˡ ⊕ᴸ =
  world (X⊑★ ∷ μ) (keep (relabel suc η)) (skip η′)
        (shiftᴸ ϱᵍ) (shiftᴸ ϱˡ)

-- W ⊕ᴿ X — the right side alone binds X: in η′'s image only (used by
-- no rule of §12.3; recorded for completeness)
_⊕ᴿ_ : World Δ Δ′ → VarImp → World Δ (underΛ Δ′)
world μ η η′ ϱᵍ ϱˡ ⊕ᴿ m =
  world (m ∷ μ) (skip η) (keep (relabel suc η′))
        (shiftᴿ ϱᵍ) (shiftᴿ ϱˡ)

-- the premise world of `∀⊑⟪+⟫`: the left opens its ∀-value under a
-- Λ-like binder (an abstract rep. var at 0), the right is inside its
-- boundary `bind 0 β`; one new center name with mark m, and the left
-- abstract rep. var is paired lexically with β (design.md §12.2, D16)
infixl 6 _⊕⁺_^_
_⊕⁺_^_ : World Δ Δ′ → VarImp → (β : RVar)
  → World (underΛ Δ) (reps Δ′ ∣ (β ∷ names Δ′))
world μ η η′ ϱᵍ ϱˡ ⊕⁺ m ^ β =
  world (m ∷ μ) (keep (relabel suc η)) (keep η′)
        (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ)

-- Renumbering on allocation (for the metatheory; no rule of §12.3
-- reads a world under an allocation).  An unmatched allocation only
-- renumbers its own side; a matched pair of TyBetas adds (0, 0) to
-- ϱᵍ; a left TyBeta catching up with a right boundary `bind 0 β`
-- that `∀⊑⟪+⟫` related adds (0, β) (design.md §12.2, D16).
allocᴸ : (R : Ty) → World Δ Δ′ → World (allocate R Δ) Δ′
allocᴸ R (world μ η η′ ϱᵍ ϱˡ) =
  world μ (relabel suc η) η′ (shiftᴸ ϱᵍ) (shiftᴸ ϱˡ)

allocᴿ : (R′ : Ty) → World Δ Δ′ → World Δ (allocate R′ Δ′)
allocᴿ R′ (world μ η η′ ϱᵍ ϱˡ) =
  world μ η (relabel suc η′) (shiftᴿ ϱᵍ) (shiftᴿ ϱˡ)

alloc² : (R R′ : Ty) → World Δ Δ′
  → World (allocate R Δ) (allocate R′ Δ′)
alloc² R R′ (world μ η η′ ϱᵍ ϱˡ) =
  world μ (relabel suc η) (relabel suc η′)
        ((zero , zero) ∷ shift² ϱᵍ) (shift² ϱˡ)

-- The two ν-bound rep. vars are in scope only while their conversions
-- are compared.  Unlike `alloc²`, which records matched runtime
-- allocations globally, this operation records (0, 0) lexically.
underν² : (R R′ : Ty) → World Δ Δ′
  → World (allocate R Δ) (allocate R′ Δ′)
underν² R R′ (world μ η η′ ϱᵍ ϱˡ) =
  world μ (relabel suc η) (relabel suc η′)
        (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ)

allocᴸ⇔ : (R : Ty) (β : RVar) → World Δ Δ′ → World (allocate R Δ) Δ′
allocᴸ⇔ R β (world μ η η′ ϱᵍ ϱˡ) =
  world μ (relabel suc η) η′ ((zero , β) ∷ shiftᴸ ϱᵍ) (shiftᴸ ϱˡ)

------------------------------------------------------------------------
-- 6. The interior world W[δ ∥ δ′] (a relation; design.md §12.2)
------------------------------------------------------------------------

-- `Interior W Θ Θ′ Wᵢ`: Wᵢ is an interior world of the boundary pair
-- `[Θ] ⊑ [Θ′]` in W.  A one-sided boundary is the case Θ = [] or
-- Θ′ = [] (W[δ ∥ ·], W[· ∥ δ′]); `toExt [] X = just X`, so every name
-- of the side without a boundary continues.
record Interior (W : World Δ Δ′) (Θ Θ′ : Boundary)
    (Wᵢ : World Δᵢ Δ′ᵢ) : Set where
  constructor interior-world
  field
    -- each side's changes act on that side's names
    int-left  : Δ ⊢ⁱ Θ ⇒ Δᵢ
    int-right : Δ′ ⊢ⁱ Θ′ ⇒ Δ′ᵢ
    -- a boundary relates no new rep. vars
    same-ϱᵍ : ϱᵍʷ Wᵢ ≡ ϱᵍʷ W
    same-ϱˡ : ϱˡʷ Wᵢ ≡ ϱˡʷ W
    -- two continuing names share a center name inside iff outside
    join-cont : ∀ {X X′ Xₑ X′ₑ}
      → Δᵢ ∋tv X → Δ′ᵢ ∋tv X′
      → toExt Θ X ≡ just Xₑ → toExt Θ′ X′ ≡ just X′ₑ
      → (Joins Wᵢ X X′ → Joins W Xₑ X′ₑ)
        × (Joins W Xₑ X′ₑ → Joins Wᵢ X X′)
    -- a name the boundary introduces joins exactly the other side's
    -- name of a paired rep. var (D25: a right `+X^β` rejoins the left
    -- partner of β whose name is in scope; `wf-namedᴸ` of Wᵢ makes it
    -- unique); otherwise it is one-sided
    join-fresh : ∀ {X X′ α β}
      → Δᵢ ∋ᵗ X := α → Δ′ᵢ ∋ᵗ X′ := β
      → Fresh Θ X ⊎ Fresh Θ′ X′
      → (Joins Wᵢ X X′ → Paired W α β)
        × (Paired W α β → Joins Wᵢ X X′)
    -- a continuing name keeps its mark, also when it went one-sided
    -- and rejoined within the entries (D15)
    mark-left : ∀ {X Xₑ m}
      → Δᵢ ∋tv X → toExt Θ X ≡ just Xₑ
      → μʷ W ∋ˡ emb (ηᴸʷ W) Xₑ := m
      → μʷ Wᵢ ∋ˡ emb (ηᴸʷ Wᵢ) X := m
    mark-right : ∀ {X′ X′ₑ m}
      → Δ′ᵢ ∋tv X′ → toExt Θ′ X′ ≡ just X′ₑ
      → μʷ W ∋ˡ emb (ηᴿʷ W) X′ₑ := m
      → μʷ Wᵢ ∋ˡ emb (ηᴿʷ Wᵢ) X′ := m
open Interior public

-- `ConversionInterior W Θ Θ′ Wᶜ`: Wᶜ relates the two contexts in
-- which the boundary conversions are read.  Those contexts keep every
-- exterior name and add a name for each newly encountered rep. var;
-- an unbind never removes a conversion-context name.  Consequently a
-- name continues exactly when its rep. var already has an exterior
-- name, and it is fresh exactly when that rep. var has none.
record ConversionInterior (W : World Δ Δ′) (Θ Θ′ : Boundary)
    (Wᶜ : World Δᶜ Δ′ᶜ) : Set where
  constructor conversion-interior-world
  field
    conv-left  : Δ ⊢ᶜ Θ ⇒ Δᶜ
    conv-right : Δ′ ⊢ᶜ Θ′ ⇒ Δ′ᶜ
    conv-same-ϱᵍ : ϱᵍʷ Wᶜ ≡ ϱᵍʷ W
    conv-same-ϱˡ : ϱˡʷ Wᶜ ≡ ϱˡʷ W
    conv-join-cont : ∀ {X X′ Xₑ X′ₑ α β}
      → Δᶜ ∋ᵗ X := α → Δ′ᶜ ∋ᵗ X′ := β
      → Δ ∋ᵗ Xₑ := α → Δ′ ∋ᵗ X′ₑ := β
      → (Joins Wᶜ X X′ → Joins W Xₑ X′ₑ)
        × (Joins W Xₑ X′ₑ → Joins Wᶜ X X′)
    conv-join-fresh : ∀ {X X′ α β}
      → Δᶜ ∋ᵗ X := α → Δ′ᶜ ∋ᵗ X′ := β
      → (names Δ ∌ʳ α) ⊎ (names Δ′ ∌ʳ β)
      → (Joins Wᶜ X X′ → Paired W α β)
        × (Paired W α β → Joins Wᶜ X X′)
    conv-mark-left : ∀ {X Xₑ α m}
      → Δᶜ ∋ᵗ X := α → Δ ∋ᵗ Xₑ := α
      → μʷ W ∋ˡ emb (ηᴸʷ W) Xₑ := m
      → μʷ Wᶜ ∋ˡ emb (ηᴸʷ Wᶜ) X := m
    conv-mark-right : ∀ {X′ X′ₑ β m}
      → Δ′ᶜ ∋ᵗ X′ := β → Δ′ ∋ᵗ X′ₑ := β
      → μʷ W ∋ˡ emb (ηᴿʷ W) X′ₑ := m
      → μʷ Wᶜ ∋ˡ emb (ηᴿʷ Wᶜ) X′ := m
open ConversionInterior public

------------------------------------------------------------------------
-- 7. Term-context imprecision (GTSFImp `CtxImp`)
------------------------------------------------------------------------

record CtxImpEntry (W : World Δ Δ′) : Set where
  constructor ctx-imp
  field
    tyᴸ  : Ty
    tyᴿ  : Ty
    impʷ : tyᴸ ⊑ᵂ⟨ W ⟩ tyᴿ
open CtxImpEntry public

CtxImp : World Δ Δ′ → Set
CtxImp W = List (CtxImpEntry W)

-- the two term contexts (Terms.Ctx = List Ty)
lhs : {W : World Δ Δ′} → CtxImp W → List Ty
lhs = map tyᴸ

rhs : {W : World Δ Δ′} → CtxImp W → List Ty
rhs = map tyᴿ

infix 4 _∋ʷ_⦂_
data _∋ʷ_⦂_ {W : World Δ Δ′} : CtxImp W → ℕ → CtxImpEntry W → Set where
  Zʷ : ∀ {γ e} → (e ∷ γ) ∋ʷ zero ⦂ e
  Sʷ : ∀ {γ e e′ x} → γ ∋ʷ x ⦂ e → (e′ ∷ γ) ∋ʷ suc x ⦂ e

-- `⇑γ` for `Λ⊑Λ`: both types shifted, the proof any at the new world
data LiftCtx {W : World Δ Δ′} (m : VarImp)
    : CtxImp W → CtxImp (W ⊕ m) → Set where
  lift-[] : LiftCtx m [] []
  lift-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtx m γ γ′
    → LiftCtx m (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) (⇑ᵗ A′) p′ ∷ γ′)

-- `⇑ᴸγ` for `Λ⊑`: the right types cross unweakened
data LiftCtxᴸ {W : World Δ Δ′} : CtxImp W → CtxImp (W ⊕ᴸ) → Set where
  liftᴸ-[] : LiftCtxᴸ [] []
  liftᴸ-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtxᴸ γ γ′
    → LiftCtxᴸ (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) A′ p′ ∷ γ′)

------------------------------------------------------------------------
-- 8. Well-formedness (design.md §12.2), a SEPARATE predicate
------------------------------------------------------------------------

-- The two embeddings jointly: every center name is in at least one
-- image (no skip/skip); a left-only name is X⊑★; a name in both images
-- names paired rep. vars ("names name paired rep. vars").
data Joint (P : RVar → RVar → Set)
    : ∀ {η η′ Ω} → η ↪ Ω → η′ ↪ Ω → Set where
  joint[]    : Joint P []↪ []↪
  both       : ∀ {α β m η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω}
    → P α β → Joint P ι ι′
    → Joint P (keep {α = α} {m = m} ι) (keep {α = β} {m = m} ι′)
  left-only  : ∀ {α η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω}
    → Joint P ι ι′
    → Joint P (keep {α = α} {m = X⊑★} ι) (skip {m = X⊑★} ι′)
  right-only : ∀ {β m η η′ Ω} {ι : η ↪ Ω} {ι′ : η′ ↪ Ω}
    → Joint P ι ι′
    → Joint P (skip {m = m} ι) (keep {α = β} {m = m} ι′)

-- Representation imprecision `μ ⊢ R ⊑ᴿ⟨ W ⟩ R′` (design.md D23): two
-- payloads compared in the representation universe (Ctx §4).  μ holds
-- one mark per local ∀-bound variable, shared by both sides as in
-- `_⊢_⊑_` (index < length μ is local); index `length μ + α` is the
-- free rep. var α.  The rules are `_⊢_⊑_`'s, with `X⊑X` split into a
-- local case and a free case (paired through ϱ = ϱᵍ ∪ ϱˡ), and one
-- extra case: a free left rep. var against ★ (`α⊑★`, no condition:
-- a rep. var carries no mark; marks belong to names, D11/D12).
data RepImp (W : World Δ Δ′) : ImpEnv → Ty → Ty → Set
infix 4 RepImp
syntax RepImp W μ R R′ = μ ⊢ R ⊑ᴿ⟨ W ⟩ R′

data RepImp W where
  ★⊑★ : ∀ {μ} → μ ⊢ ★ ⊑ᴿ⟨ W ⟩ ★
  ι⊑ι : ∀ {μ ι} → Base ι → μ ⊢ ι ⊑ᴿ⟨ W ⟩ ι
  X⊑X : ∀ {μ X m} → μ ∋ˡ X := m → μ ⊢ ` X ⊑ᴿ⟨ W ⟩ ` X
  α⊑β : ∀ {μ α β} → Paired W α β
    → μ ⊢ ` (length μ + α) ⊑ᴿ⟨ W ⟩ ` (length μ + β)
  ⇒⊑⇒ : ∀ {μ R R′ S S′}
    → μ ⊢ R ⊑ᴿ⟨ W ⟩ R′ → μ ⊢ S ⊑ᴿ⟨ W ⟩ S′
    → μ ⊢ R ⇒ S ⊑ᴿ⟨ W ⟩ R′ ⇒ S′
  ∀⊑∀ : ∀ {μ R R′} → extᵐ μ ⊢ R ⊑ᴿ⟨ W ⟩ R′ → μ ⊢ `∀ R ⊑ᴿ⟨ W ⟩ `∀ R′
  ⇒⊑★ : ∀ {μ R S}
    → μ ⊢ R ⊑ᴿ⟨ W ⟩ ★ → μ ⊢ S ⊑ᴿ⟨ W ⟩ ★ → μ ⊢ R ⇒ S ⊑ᴿ⟨ W ⟩ ★
  ι⊑★ : ∀ {μ ι} → Base ι → μ ⊢ ι ⊑ᴿ⟨ W ⟩ ★
  X⊑★ : ∀ {μ X} → μ ∋ˡ X := X⊑★ → μ ⊢ ` X ⊑ᴿ⟨ W ⟩ ★
  α⊑★ : ∀ {μ α} → μ ⊢ ` (length μ + α) ⊑ᴿ⟨ W ⟩ ★
  ∀⊑  : ∀ {μ R R′} → NonVar R → 0 ∈ᵗ R
    → instᵐ μ ⊢ R ⊑ᴿ⟨ W ⟩ ⇑ᵗ R′ → μ ⊢ `∀ R ⊑ᴿ⟨ W ⟩ R′
  ∀★⊑★ : ∀ {μ} → μ ⊢ `∀ ★ ⊑ᴿ⟨ W ⟩ ★
  ∀⊑★ : ∀ {μ R} → NonStar R → extᵐ μ ⊢ R ⊑ᴿ⟨ W ⟩ ★
    → μ ⊢ `∀ R ⊑ᴿ⟨ W ⟩ ★
  bot-elim : ∀ {μ} → μ ⊢ `∀ (` 0) ⊑ᴿ⟨ W ⟩ `∀ ★
  bot⊑★ : ∀ {μ} → μ ⊢ `∀ (` 0) ⊑ᴿ⟨ W ⟩ ★

-- "Paired rep. vars agree": both abstract; an abstract left rep. var
-- against β:=★; or two payloads related by `RepImp` (design.md D23)
data Agree (W : World Δ Δ′) (α β : RVar) : Set where
  abst-abst : reps Δ ∋ʳ α := abstR → reps Δ′ ∋ʳ β := abstR
    → Agree W α β
  abst-★    : reps Δ ∋ʳ α := abstR → Δ′ ∋rep β := ★
    → Agree W α β
  rep-rep   : ∀ {R R′}
    → Δ ∋rep α := R → Δ′ ∋rep β := R′
    → [] ⊢ R ⊑ᴿ⟨ W ⟩ R′
    → Agree W α β

-- Named uniqueness (design.md D25).  ϱ itself may give a rep. var
-- several partners on either side; but among the rep. vars NAMED on
-- one side, at most one is paired with a given rep. var named on the
-- other side.  This is what `Interior`'s rejoin reads: a name a
-- boundary introduces must join every other-side name in scope whose
-- rep. var is paired with its own, and an embedding joins a name to at
-- most one other name.  Rep. vars without a name in scope (store rep.
-- vars, rep. vars hidden by an unbind) are unconstrained.
NamedUniqueᴸ : World Δ Δ′ → Set
NamedUniqueᴸ {Δ} {Δ′} W = ∀ {α α′ β}
  → names Δ ∋ᵅ α → names Δ ∋ᵅ α′ → names Δ′ ∋ᵅ β
  → Paired W α β → Paired W α′ β → α ≡ α′

NamedUniqueᴿ : World Δ Δ′ → Set
NamedUniqueᴿ {Δ} {Δ′} W = ∀ {α β β′}
  → names Δ ∋ᵅ α → names Δ′ ∋ᵅ β → names Δ′ ∋ᵅ β′
  → Paired W α β → Paired W α β′ → β ≡ β′

record WfWorld (W : World Δ Δ′) : Set where
  constructor wf-world
  field
    wf-joint : Joint (Paired W) (ηᴸʷ W) (ηᴿʷ W)
    wf-agree : ∀ {α β} → Paired W α β → Agree W α β
    -- D25 (replaces D13's one-left-partner rule): named uniqueness
    wf-namedᴸ : NamedUniqueᴸ W
    wf-namedᴿ : NamedUniqueᴿ W
open WfWorld public
