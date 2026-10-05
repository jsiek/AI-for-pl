module ImprecisionWorld where

-- File Charter:
--   * THE WORLDS OF CAST-TERM IMPRECISION (GTNF/design.md §12.2;
--     D12-D16, D25, D27, D28).  §1 order-preserving embeddings of name
--     positions `_↪_` into a center of n names (GTSFImp's `_↪ᵗ_` with
--     `keep`/`skip`) and their renaming `emb`; the PERMISSION `permit`
--     of a right rep. var and the DERIVED MARKS `dmarks`; §2 the rep.
--     var correspondence `RepRel` and its renumberings; §3 `World`,
--     `marksʷ`, `Paired` (ϱ = ϱᵍ ∪ ϱˡ) and R1/R2's condition
--     `Unpermitted`/`LeftUnpermitted`/`UnbindOK` (design.md D28); §4
--     type imprecision at a world `_⊑ᵂ⟨_⟩_`; §5 the world operations
--     `W ⊕²`, `W ⊕ᴸ`, `W ⊕ᴿ`, `W ⊕⁺^ β`, `W ⊕ʳ^ β`, `Join↪`/`Open1`
--     (one pending name popped by a left binder, design.md D27), the
--     allocation renumberings, and `underν²`; §6 the term-interior
--     world `Interior W Θ Θ′ Wᵢ` and conversion-context world
--     `ConversionInterior W Θ Θ′ Wᶜ`, both RELATIONS; §7 term-context
--     imprecision `CtxImp`, `LiftCtx`, `LiftCtxᴸ`, `RaiseCtx`; §8
--     well-formedness `WfWorld`, a SEPARATE predicate, with payload
--     imprecision `RepImp` (D23), named uniqueness
--     `NamedUniqueᴸ`/`NamedUniqueᴿ` (D25), the conditions on pending
--     names (`PendingOK`, D27) and on permissions (`wf-permits`, D28).
--   * MARKS ARE COMPUTED, NOT STORED (design.md D28; Jeremy,
--     2026-10-05; checked first as proof/DGG/notes/Permissions.agda
--     and PermissionsR.agda).  A world has a field `κʷ`, the PERMITTED
--     right rep. vars, and the mark of a center name is
--     `marksʷ W = dmarks (ηᴿʷ W) (κʷ W)`: a name the right does not see
--     (left-only) is X⊑★; a name the right sees is X⊑★ iff its right
--     rep. var is in κʷ, else X⊑X.  A right check `X?` (TermImprecision
--     `⊑cast` with `CastGrant`) adds X's rep. var to κʷ of its premise
--     world: an X-tagged right value may face an untagged left value
--     only below a right check of X.  The center is a number `Ωʷ`
--     (nothing stores a mark), so a grant is `record W { κʷ = β ∷ κʷ W }`
--     and leaves the embeddings, `Paired`, `Joins`, `Interior` and `πʷ`
--     unchanged definitionally.  This supersedes D11 (marks chosen at
--     the binder) and D15's "a continuing name keeps its mark".
--   * PENDING NAMES ARE A FIELD OF THE WORLD (design.md D27; Jeremy,
--     2026-10-05).  `πʷ W` lists the PENDING right names (positions in
--     `names Δ′`), next pop first: right-only names that a `⊑⟪⟫` pushed
--     and that a left binder will join.  There is one world type and
--     one index `_⊑ᵂ⟨_⟩_`, which opens one left `∀` per pending name
--     (`OpenImp`); at `πʷ W = []` it is
--     `marksʷ W ⊢ embᴸ W A ⊑ embᴿ W A′` definitionally.  Everything
--     that does not concern pending names reads only the other fields
--     (`Paired`, `Joins`, `Interior`, `CtxImp`), so updating `πʷ`
--     (`record W { πʷ = π }`) leaves them unchanged definitionally
--     (record eta), with no transport.
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
--     design.md §12.2).
--   * REPRESENTATION CHOICES.
--     - A world is indexed by the two type contexts `Δ` (left, more
--       precise) and `Δ′` (right).
--     - THE CENTER Ω IS A NUMBER `Ωʷ`; a center name is a position
--       below it.  The embeddings are indexed by `names Δ` and by Ωʷ,
--       so they cover every name in scope by construction.  `emb` is
--       the identity past the end (only in-range positions are read).
--     - ϱ is two lists of pairs (left rep. var, right rep. var) over the
--       CURRENT de Bruijn rep. vars of the two sides: `ϱᵍʷ` (global,
--       store rep. vars) and `ϱˡʷ` (lexical, rep. vars bound by an
--       enclosing Λ, or by the pop of a pending name, D27).  A binder
--       or an allocation renumbers the side it acts on; κʷ (right rep.
--       vars) is renumbered with the right side.
--     - `Interior` is declarative.  A continuing name (one `toExt` sends
--       to an exterior position) keeps its center partner; a name the
--       boundary itself introduces (`Fresh`) joins the other side's
--       name exactly when their rep. vars are paired by ϱ (D25: a right
--       `+X^β` rejoins the left partner of β whose name is in scope; ϱ
--       may give β several partners, named uniqueness in `WfWorld`
--       keeps the rejoin unique).  A boundary keeps ϱ and κ (`same-ϱᵍ`,
--       `same-ϱˡ`, `same-κ`), so the marks of continuing names follow
--       from their joins (D28).  Nothing is said about the worlds
--       between the entries.
--   * PAYLOADS ARE COMPARED IN THE REPRESENTATION UNIVERSE (design.md
--     D23; Jeremy, 2026-10-03).  `Agree.rep-rep` relates two payloads
--     by `RepImp` (§8, `μ ⊢ R ⊑ᴿ⟨ W ⟩ R′`): free rep. vars correspond
--     through `Paired W`, local ∀-bound variables position-wise with
--     marks.  This replaces the earlier deviation that read payloads
--     as ordinary types through each side's names, which failed for a
--     payload mentioning a rep. var hidden by a boundary
--     (proof/DGG/drafts/EvolveImpWfInteriorCounterexample.agda).
--   * R1/R2's CONDITION (design.md D28).  `Unpermitted W α`: the LEFT
--     rep. var α has no permitted right partner.  TermImprecision's
--     `⟪⟫⊑` takes it for every left unbind of its boundary
--     (`UnbindOK`, R1); ConversionImprecision's four ★ clauses take it
--     for the left name (`LeftUnpermitted`, R2).  They are RULE
--     premises, not WfWorld fields: no condition on worlds alone
--     separates C5's hidden variant from P4 B3
--     (proof/DGG/notes/PermissionsR.md §1.4).
--   * DEVIATIONS from design.md §12.2 (each also in the report):
--     - `Interior` does not require `WfWorld Wᵢ`, although §12.2 says
--       W[δ ∥ δ′] "is defined only when it is well formed": WfWorld is
--       kept separate (only the final world Wᵢ would be constrained,
--       D15), and the rules read only the joins fixed here.
--     - `W ⊕⁺^ β` (the premise world of the pop of the pending name of
--       the right entry `bind 0 β`, `open-⊕`) is its own operation:
--       the right side's new name is the boundary entry `bind 0 β`, not
--       a Λ, so the right context is `reps Δ′ ∣ β ∷ names Δ′`, not
--       `underΛ Δ′`; the lexical pair is (0, β).
--   * HISTORY (design.md D26, 2026-10-03; D27, 2026-10-05; D28,
--     2026-10-05).  Before D26 the term relation had a separate rule
--     `∀⊑⟪+⟫` whose premise world was `W ⊕⁺ m ^ β`; D26 removed it in
--     favour of the openings of `⊑⟪⟫` (`Open1`, here; `Opens`,
--     TermImprecision); D27 replaced `Opens` by pending names in the
--     world (`πʷ`), popped by `Open1`.  Before D28 the center was the
--     mark list `μʷ`, every binder and boundary-introduced name chose
--     its mark (D11), `Interior` kept continuing marks (D15) and a
--     pending name was fixed at X⊑★; D28 derives every mark from κʷ.
--     - `ConversionInterior`, like `Interior`, does not require
--       `WfWorld Wᶜ`.  A conversion context is the union of names live
--       anywhere along a boundary, so continuation/freshness is stated
--       by whether the name's rep. var already has an exterior name,
--       rather than by `toExt` on the term-interior context.

open import Data.Bool using (if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (_+_)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.List.Relation.Unary.AllPairs using (AllPairs; [])
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
  using (Ty; `_; `ℕ; `𝔹; ★; _⇒_; `∀; Base; Renameᵗ; renameᵗ; ⇑ᵗ)
open import Ctx
open import Boundary using (Boundary; Change; bind; unbind;
  _⊢ⁱ_⇒_; _⊢ᶜ_⇒_; toExt; Fresh)
open import Imprecision
  using (VarImp; X⊑X; X⊑★; ImpEnv; extᵐ; instᵐ; _⊢_⊑_)
open import Coercion using (NonVar; NonStar; _∈ᵗ_)

private
  variable
    Δ Δ′ Δᵢ Δ′ᵢ Δᶜ Δ′ᶜ : Ctxᵗ

------------------------------------------------------------------------
-- 1. Embeddings of name positions into the center; derived marks
------------------------------------------------------------------------

-- `η : names Δ ↪ n`: an order-preserving embedding of Δ's name
-- positions into a center of n names (GTSFImp `_↪ᵗ_`).  `keep` sends
-- the next name to the next center name; `skip` passes a center name
-- this side does not see.
infix 4 _↪_
data _↪_ : TyCtx → ℕ → Set where
  []↪  : [] ↪ 0
  keep : ∀ {α Δ n} → Δ ↪ n → (α ∷ Δ) ↪ suc n
  skip : ∀ {Δ n} → Δ ↪ n → Δ ↪ suc n

-- its renaming (GTSFImp `toRenameᵗ`)
emb : ∀ {η n} → η ↪ n → Renameᵗ
emb []↪      X       = X
emb (keep ι) zero    = zero
emb (keep ι) (suc X) = suc (emb ι X)
emb (skip ι) X       = suc (emb ι X)

-- a renumbering of the rep. vars the names denote moves no position
relabel : ∀ {η n} (f : RVar → RVar) → η ↪ n → map f η ↪ n
relabel f []↪      = []↪
relabel f (keep ι) = keep (relabel f ι)
relabel f (skip ι) = skip (relabel f ι)

-- THE PERMISSION of one right rep. var (design.md D28): X⊑★ when it is
-- in the permitted list, else X⊑X
permit : RVar → List RVar → VarImp
permit β []      = X⊑X
permit β (γ ∷ κ) = if β ≡ᵇ γ then X⊑★ else permit β κ

-- THE DERIVED MARKS: a center name the right sees has its right rep.
-- var's permission; a center name the right does not see (left-only)
-- is X⊑★
dmarks : ∀ {ns n} → ns ↪ n → List RVar → ImpEnv
dmarks []↪              κ = []
dmarks (keep {α = β} ι) κ = permit β κ ∷ dmarks ι κ
dmarks (skip ι)         κ = X⊑★ ∷ dmarks ι κ

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
    Ωʷ  : ℕ                     -- the center: how many center names
    ηᴸʷ : names Δ ↪ Ωʷ          -- the left names
    ηᴿʷ : names Δ′ ↪ Ωʷ         -- the right names
    ϱᵍʷ : RepRel                -- global: store rep. vars (D16)
    ϱˡʷ : RepRel                -- lexical: Λ- and boundary-bound (D16)
    κʷ  : List RVar             -- permitted right rep. vars (D28)
    πʷ  : List ℕ                -- pending right names, next pop first (D27)
open World public

-- THE MARKS of the center names, derived (design.md D28)
marksʷ : World Δ Δ′ → ImpEnv
marksʷ W = dmarks (ηᴿʷ W) (κʷ W)

-- ϱ = ϱᵍ ∪ ϱˡ
Paired : World Δ Δ′ → RVar → RVar → Set
Paired W α β = (ϱᵍʷ W ∋ᵨ α ⇔ β) ⊎ (ϱˡʷ W ∋ᵨ α ⇔ β)

-- a left and a right position name the same center name
Joins : World Δ Δ′ → ℕ → ℕ → Set
Joins W X X′ = emb (ηᴸʷ W) X ≡ emb (ηᴿʷ W) X′

-- a world with no permission (κ = []; every top-level world, and most
-- literal worlds of the examples)
world⁰ : ∀ {Δ Δ′} (n : ℕ) → names Δ ↪ n → names Δ′ ↪ n
  → RepRel → RepRel → List ℕ → World Δ Δ′
world⁰ n η η′ ϱᵍ ϱˡ π = world n η η′ ϱᵍ ϱˡ [] π

-- the closed world: no names, no rep. vars paired, no permission
∅ʷ : World empty empty
∅ʷ = world⁰ 0 []↪ []↪ [] [] []

-- R1/R2's CONDITION (design.md D28): the LEFT rep. var α has no
-- PERMITTED right partner (stated through `permit`, which the derived
-- marks read; equivalently ¬ ∃ β. Paired W α β × β ∈ κʷ W)
Unpermitted : World Δ Δ′ → RVar → Set
Unpermitted W α = ∀ {β} → Paired W α β → permit β (κʷ W) ≡ X⊑X

-- R2's form: the rep. var of the left name X (there is at most one)
LeftUnpermitted : World Δ Δ′ → ℕ → Set
LeftUnpermitted {Δ = Δ} W X = ∀ {α} → Δ ∋ᵗ X := α → Unpermitted W α

-- R1's form, per boundary entry: a left UNBIND of α needs α
-- unpermitted; a bind needs nothing
data UnbindOK (W : World Δ Δ′) : Change → Set where
  ok-bind   : ∀ {X α} → UnbindOK W (bind X α)
  ok-unbind : ∀ {X α} → Unpermitted W α → UnbindOK W (unbind X α)

------------------------------------------------------------------------
-- 4. Type imprecision at a world (GTSFImp `_⊑ᵂ⟨_⟩_`)
------------------------------------------------------------------------

embᴸ : World Δ Δ′ → Ty → Ty
embᴸ W = renameᵗ (emb (ηᴸʷ W))

embᴿ : World Δ Δ′ → Ty → Ty
embᴿ W = renameᵗ (emb (ηᴿʷ W))

-- one opened binder in front of a renaming: the bound variable 0 goes
-- to the center name c
infixr 5 _⊳_
_⊳_ : ℕ → Renameᵗ → Renameᵗ
(c ⊳ ρ) zero    = c
(c ⊳ ρ) (suc X) = ρ X

-- `OpenImp μ cs ρ A B`: A with its outer binders opened at the center
-- names cs (outermost first), renamed by ρ, is below B.  A non-∀ type
-- under a pending name has no index.
OpenImp : ImpEnv → List ℕ → Renameᵗ → Ty → Ty → Set
OpenImp μ []       ρ A        B = μ ⊢ renameᵗ ρ A ⊑ B
OpenImp μ (c ∷ cs) ρ (`∀ A)   B = OpenImp μ cs (c ⊳ ρ) A B
OpenImp μ (c ∷ cs) ρ (` X)    B = ⊥
OpenImp μ (c ∷ cs) ρ `ℕ       B = ⊥
OpenImp μ (c ∷ cs) ρ `𝔹       B = ⊥
OpenImp μ (c ∷ cs) ρ ★        B = ⊥
OpenImp μ (c ∷ cs) ρ (A ⇒ A′) B = ⊥

-- THE INDEX of the term relation: the actual left type, opened at the
-- center names of the pending names (design.md D27), at the derived
-- marks (D28).  With no pending name (`πʷ W = []`) it is
-- `marksʷ W ⊢ embᴸ W A ⊑ embᴿ W A′` (definitionally).
infix 4 _⊑ᵂ⟨_⟩_
_⊑ᵂ⟨_⟩_ : Ty → World Δ Δ′ → Ty → Set
A ⊑ᵂ⟨ W ⟩ A′ =
  OpenImp (marksʷ W) (map (emb (ηᴿʷ W)) (πʷ W)) (emb (ηᴸʷ W)) A (embᴿ W A′)

------------------------------------------------------------------------
-- 5. World operations (design.md §12.2)
------------------------------------------------------------------------

-- No operation takes a mark (they are derived, D28).  A new right name
-- 0 moves every pending name one position up; a new left name, or an
-- allocation, moves none.  A new RIGHT rep. var (a right Λ, a right
-- allocation) renumbers κ (`map suc`); a boundary entry binds no new
-- rep. var and leaves κ alone.

-- W ⊕² — both sides bind X by a Λ: a new center name in both images,
-- and the two abstract rep. vars paired lexically; the new right rep.
-- var 0 is not permitted, so X is X⊑X
infixl 6 _⊕² _⊕ᴸ _⊕ᴿ _⊕⁺^_ _⊕ʳ^_
_⊕² : World Δ Δ′ → World (underΛ Δ) (underΛ Δ′)
world n η η′ ϱᵍ ϱˡ κ π ⊕² =
  world (suc n) (keep (relabel suc η)) (keep (relabel suc η′))
        (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ) (map suc κ) (map suc π)

-- W ⊕ᴸ — the left side alone binds X: in η's image only (so X⊑★);
-- its abstract rep. var is unpaired
_⊕ᴸ : World Δ Δ′ → World (underΛ Δ) Δ′
world n η η′ ϱᵍ ϱˡ κ π ⊕ᴸ =
  world (suc n) (keep (relabel suc η)) (skip η′)
        (shiftᴸ ϱᵍ) (shiftᴸ ϱˡ) κ π

-- W ⊕ᴿ — the right side alone binds X: in η′'s image only (used by
-- no rule of §12.3; recorded for completeness)
_⊕ᴿ : World Δ Δ′ → World Δ (underΛ Δ′)
world n η η′ ϱᵍ ϱˡ κ π ⊕ᴿ =
  world (suc n) (skip η) (keep (relabel suc η′))
        (shiftᴿ ϱᵍ) (shiftᴿ ϱˡ) (map suc κ) (map suc π)

-- the premise world of the pop of the pending name of `bind 0 β`
-- (`open-⊕`, design.md D27): the left goes under its binder, a Λ-like
-- binder (an abstract rep. var at 0), the right is inside its boundary
-- `bind 0 β`; one new center name, and the left abstract rep. var is
-- paired lexically with β (design.md §12.2, D16)
_⊕⁺^_ : World Δ Δ′ → (β : RVar)
  → World (underΛ Δ) (reps Δ′ ∣ (β ∷ names Δ′))
world n η η′ ϱᵍ ϱˡ κ π ⊕⁺^ β =
  world (suc n) (keep (relabel suc η)) (keep η′)
        (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) κ (map suc π)

-- the interior world of `⊑⟪⟫` at a single right entry `bind 0 β`
-- (`+X^β`): X is a right-only name (FixB's `_⊕ʳ_^_`)
_⊕ʳ^_ : World Δ Δ′ → (β : RVar) → World Δ (reps Δ′ ∣ (β ∷ names Δ′))
world n η η′ ϱᵍ ϱˡ κ π ⊕ʳ^ β =
  world (suc n) (skip η) (keep η′) ϱᵍ ϱˡ κ (map suc π)

-- POPS (design.md D27; D26's openings).  A left binder (`Λ⊑`, or the
-- gen layer of `cast⊑`) may join the pending right-only name k that a
-- `⊑⟪⟫` pushed: the binder (a Λ-like abstract rep. var at 0, as
-- `underΛ`) joins k's center name.  `Join↪ ι ι′ ι⁺ k`: the left's NEW
-- name 0 is kept into the center name of the right's name k, which is
-- RIGHT-ONLY; the center names before it are right-only too (the left
-- skips them), so the left's order is preserved.  `ι⁺` is the left
-- embedding after the pop (FixB's `JoinΛ`, at any position k).
data Join↪ {η : TyCtx}
    : ∀ {η′ n} → η ↪ n → η′ ↪ n → (zero ∷ map suc η) ↪ n → ℕ → Set where
  join-here : ∀ {β η′ n} {ι : η ↪ n} {ι′ : η′ ↪ n}
    → Join↪ (skip ι) (keep {α = β} ι′) (keep (relabel suc ι)) zero
  join-there : ∀ {β η′ n k} {ι : η ↪ n} {ι′ : η′ ↪ n}
      {ι⁺ : (zero ∷ map suc η) ↪ n}
    → Join↪ ι ι′ ι⁺ k
    → Join↪ (skip ι) (keep {α = β} ι′) (skip ι⁺) (suc k)

-- The pop of the head pending name k, whose rep. var β is bound to ★;
-- the left abstract rep. var is paired with β LEXICALLY (D16).  The
-- right does not move, so κ is unchanged.  `W ⊕⁺^ β` is the pop of
-- name 0 of `W ⊕ʳ^ β` with 0 pushed (`open-⊕`).
data Open1 {Δ Δ′ : Ctxᵗ} : World Δ Δ′ → World (underΛ Δ) Δ′ → Set where
  open1 : ∀ {n ϱᵍ ϱˡ κ k π β} {ι : names Δ ↪ n} {ι′ : names Δ′ ↪ n}
      {ι⁺ : names (underΛ Δ) ↪ n}
    → Join↪ ι ι′ ι⁺ k
    → Δ′ ∋ᵗ k := β
    → Δ′ ∋rep β := ★
    → Open1 (world n ι ι′ ϱᵍ ϱˡ κ (k ∷ π))
            (world n ι⁺ ι′ (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) κ π)

open-⊕ : ∀ {W : World Δ Δ′} {β}
  → Δ′ ∋rep β := ★
  → Open1 (record (W ⊕ʳ^ β) { πʷ = 0 ∷ map suc (πʷ W) }) (W ⊕⁺^ β)
open-⊕ hβ = open1 join-here here hβ

-- Renumbering on allocation (for the metatheory; no rule of §12.3
-- reads a world under an allocation).  An unmatched allocation only
-- renumbers its own side (κ with the right side); a matched pair of
-- TyBetas adds (0, 0) to ϱᵍ; a left TyBeta catching up with a right
-- boundary `bind 0 β` whose name a left binder popped adds (0, β)
-- (design.md §12.2, D16, D27).
allocᴸ : (R : Ty) → World Δ Δ′ → World (allocate R Δ) Δ′
allocᴸ R (world n η η′ ϱᵍ ϱˡ κ π) =
  world n (relabel suc η) η′ (shiftᴸ ϱᵍ) (shiftᴸ ϱˡ) κ π

allocᴿ : (R′ : Ty) → World Δ Δ′ → World Δ (allocate R′ Δ′)
allocᴿ R′ (world n η η′ ϱᵍ ϱˡ κ π) =
  world n η (relabel suc η′) (shiftᴿ ϱᵍ) (shiftᴿ ϱˡ) (map suc κ) π

alloc² : (R R′ : Ty) → World Δ Δ′
  → World (allocate R Δ) (allocate R′ Δ′)
alloc² R R′ (world n η η′ ϱᵍ ϱˡ κ π) =
  world n (relabel suc η) (relabel suc η′)
        ((zero , zero) ∷ shift² ϱᵍ) (shift² ϱˡ) (map suc κ) π

-- The two ν-bound rep. vars are in scope only while their conversions
-- are compared.  Unlike `alloc²`, which records matched runtime
-- allocations globally, this operation records (0, 0) lexically.
underν² : (R R′ : Ty) → World Δ Δ′
  → World (allocate R Δ) (allocate R′ Δ′)
underν² R R′ (world n η η′ ϱᵍ ϱˡ κ π) =
  world n (relabel suc η) (relabel suc η′)
        (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ) (map suc κ) π

allocᴸ⇔ : (R : Ty) (β : RVar) → World Δ Δ′ → World (allocate R Δ) Δ′
allocᴸ⇔ R β (world n η η′ ϱᵍ ϱˡ κ π) =
  world n (relabel suc η) η′ ((zero , β) ∷ shiftᴸ ϱᵍ) (shiftᴸ ϱˡ) κ π

------------------------------------------------------------------------
-- 6. The interior world W[δ ∥ δ′] (a relation; design.md §12.2)
------------------------------------------------------------------------

-- `Interior W Θ Θ′ Wᵢ`: Wᵢ is an interior world of the boundary pair
-- `[Θ] ⊑ [Θ′]` in W.  A one-sided boundary is the case Θ = [] or
-- Θ′ = [] (W[δ ∥ ·], W[· ∥ δ′]); `toExt [] X = just X`, so every name
-- of the side without a boundary continues.  There are no mark fields:
-- the marks are derived from the joins and κ, which a boundary keeps
-- (design.md D28; D11's choice and D15's keep-on-rejoin are gone).
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
    -- a boundary moves no rep. var: the permissions pass through (D28)
    same-κ  : κʷ Wᵢ ≡ κʷ W
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
    conv-same-κ  : κʷ Wᶜ ≡ κʷ W
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
open ConversionInterior public

------------------------------------------------------------------------
-- 7. Term-context imprecision (GTSFImp `CtxImp`)
------------------------------------------------------------------------

-- An entry reads the marks, the center and the two embeddings (not ϱ,
-- not the pending names).  The marks are a parameter of their own (they
-- are derived from ηᴿ and κ), so `CtxImp (record W { πʷ = π })` IS
-- `CtxImp W`, while a grant moves the entries by `RaiseCtx`.
record CtxImpEntry {ns ns′ : TyCtx} {n : ℕ} (μ : ImpEnv) (ηᴸ : ns ↪ n)
    (ηᴿ : ns′ ↪ n) : Set where
  constructor ctx-imp
  field
    tyᴸ  : Ty
    tyᴿ  : Ty
    impʷ : μ ⊢ renameᵗ (emb ηᴸ) tyᴸ ⊑ renameᵗ (emb ηᴿ) tyᴿ
open CtxImpEntry public

-- term-context imprecision at μ, ηᴸ, ηᴿ
Entries : ∀ {ns ns′ n} (μ : ImpEnv) → ns ↪ n → ns′ ↪ n → Set
Entries μ ηᴸ ηᴿ = List (CtxImpEntry μ ηᴸ ηᴿ)

-- the entries are read at the derived marks: CtxImp depends on κʷ (not
-- on πʷ)
CtxImp : World Δ Δ′ → Set
CtxImp W = Entries (marksʷ W) (ηᴸʷ W) (ηᴿʷ W)

-- the two term contexts (Terms.Ctx = List Ty)
lhs : ∀ {ns ns′ n μ} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
  → Entries μ ηᴸ ηᴿ → List Ty
lhs = map tyᴸ

rhs : ∀ {ns ns′ n μ} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
  → Entries μ ηᴸ ηᴿ → List Ty
rhs = map tyᴿ

infix 4 _∋ʷ_⦂_
data _∋ʷ_⦂_ {ns ns′ n μ} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    : Entries μ ηᴸ ηᴿ → ℕ → CtxImpEntry μ ηᴸ ηᴿ → Set where
  Zʷ : ∀ {γ e} → (e ∷ γ) ∋ʷ zero ⦂ e
  Sʷ : ∀ {γ e e′ x} → γ ∋ʷ x ⦂ e → (e′ ∷ γ) ∋ʷ suc x ⦂ e

-- `⇑γ` for `Λ⊑Λ`: both types shifted, the proof any at the new world
-- (`CtxImp W → CtxImp (W ⊕²)`)
data LiftCtx {ns ns′ n μ ns₁ ns′₁ n₁ μ₁} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {ηᴸ₁ : ns₁ ↪ n₁} {ηᴿ₁ : ns′₁ ↪ n₁}
    : Entries μ ηᴸ ηᴿ → Entries μ₁ ηᴸ₁ ηᴿ₁ → Set where
  lift-[] : LiftCtx [] []
  lift-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtx γ γ′
    → LiftCtx (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) (⇑ᵗ A′) p′ ∷ γ′)

-- `⇑ᴸγ` for `Λ⊑`: the right types cross unweakened.  The premise world
-- is any world over `underΛ Δ` (`W ⊕ᴸ` for a fresh left-only binder, or
-- the `Open1` of a pending name, design.md D27)
data LiftCtxᴸ {ns ns′ n μ ns₁ n₁ μ₁} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {ηᴸ₁ : ns₁ ↪ n₁} {ηᴿ₁ : ns′ ↪ n₁}
    : Entries μ ηᴸ ηᴿ → Entries μ₁ ηᴸ₁ ηᴿ₁ → Set where
  liftᴸ-[] : LiftCtxᴸ [] []
  liftᴸ-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtxᴸ γ γ′
    → LiftCtxᴸ (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) A′ p′ ∷ γ′)

-- a grant (design.md D28) raises the marks: the entries keep their
-- types, the proofs are at the raised marks (type imprecision is
-- monotone in the marks, so they always exist)
data RaiseCtx {ns ns′ n μ μ₁} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    : Entries μ ηᴸ ηᴿ → Entries μ₁ ηᴸ ηᴿ → Set where
  raise-[] : RaiseCtx [] []
  raise-∷  : ∀ {γ γ′ A A′ p p′} → RaiseCtx γ γ′
    → RaiseCtx (ctx-imp A A′ p ∷ γ) (ctx-imp A A′ p′ ∷ γ′)

raise-refl : ∀ {ns ns′ n μ} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
  (γ : Entries μ ηᴸ ηᴿ) → RaiseCtx γ γ
raise-refl []      = raise-[]
raise-refl (e ∷ γ) = raise-∷ (raise-refl γ)

------------------------------------------------------------------------
-- 8. Well-formedness (design.md §12.2), a SEPARATE predicate
------------------------------------------------------------------------

-- The two embeddings jointly: every center name is in at least one
-- image (no skip/skip); a name in both images names paired rep. vars
-- ("names name paired rep. vars").  No marks: a left-only name is
-- X⊑★ by `dmarks` (design.md D28).
data Joint (P : RVar → RVar → Set)
    : ∀ {η η′ n} → η ↪ n → η′ ↪ n → Set where
  joint[]    : Joint P []↪ []↪
  both       : ∀ {α β η η′ n} {ι : η ↪ n} {ι′ : η′ ↪ n}
    → P α β → Joint P ι ι′
    → Joint P (keep {α = α} ι) (keep {α = β} ι′)
  left-only  : ∀ {α η η′ n} {ι : η ↪ n} {ι′ : η′ ↪ n}
    → Joint P ι ι′
    → Joint P (keep {α = α} ι) (skip ι′)
  right-only : ∀ {β η η′ n} {ι : η ↪ n} {ι′ : η′ ↪ n}
    → Joint P ι ι′
    → Joint P (skip ι) (keep {α = β} ι′)

-- Representation imprecision `μ ⊢ R ⊑ᴿ⟨ W ⟩ R′` (design.md D23): two
-- payloads compared in the representation universe (Ctx §4).  μ holds
-- one mark per local ∀-bound variable, shared by both sides as in
-- `_⊢_⊑_` (index < length μ is local); index `length μ + α` is the
-- free rep. var α.  The rules are `_⊢_⊑_`'s, with `X⊑X` split into a
-- local case and a free case (paired through ϱ = ϱᵍ ∪ ϱˡ), and one
-- extra case: a free left rep. var against ★ (`α⊑★`, no condition:
-- a rep. var carries no mark; marks belong to names, D12).
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

-- β has no left partner that is named in Δ (D25's scoped analogue of
-- D13's `NoLeftPartner`; a pending name's rep. var)
NoNamedPartner : World Δ Δ′ → RVar → Set
NoNamedPartner {Δ} W β = ∀ {α} → names Δ ∋ᵅ α → ¬ Paired W α β

-- a right name no left name joins
RightOnly : World Δ Δ′ → ℕ → Set
RightOnly {Δ = Δ} W k = ∀ {X} → Δ ∋tv X → ¬ Joins W X k

-- a pending name (design.md D27): bound to a ★ rep. var β, right-only,
-- and β has no left partner with a name (so the pop keeps named
-- uniqueness, as `wf-⊕⁺`).  Its mark is derived (D28): X⊑★ exactly
-- when β is permitted.
PendingOK : World Δ Δ′ → ℕ → Set
PendingOK {Δ′ = Δ′} W k =
  Σ[ β ∈ RVar ] (Δ′ ∋ᵗ k := β) × (Δ′ ∋rep β := ★) × RightOnly W k
    × NoNamedPartner W β

record WfWorld (W : World Δ Δ′) : Set where
  constructor wf-world
  field
    wf-joint : Joint (Paired W) (ηᴸʷ W) (ηᴿʷ W)
    wf-agree : ∀ {α β} → Paired W α β → Agree W α β
    -- D25 (replaces D13's one-left-partner rule): named uniqueness
    wf-namedᴸ : NamedUniqueᴸ W
    wf-namedᴿ : NamedUniqueᴿ W
    -- D27: the pending names are pending names, and distinct
    wf-pending  : All (PendingOK W) (πʷ W)
    wf-distinct : AllPairs _≢_ (πʷ W)
    -- D28: every permitted rep. var is a right rep. var (named or not:
    -- a right hide keeps its permission, P4 B4)
    wf-permits  : All (reps Δ′ ∋ʳ_) (κʷ W)
open WfWorld public
