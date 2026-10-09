module ImprecisionWorld where

-- File Charter:
--   * THE WORLDS OF CAST-TERM IMPRECISION (GTNF/design.md §9, §10;
--     D12-D16, D25, D28, D29, D31).  §1 order-preserving embeddings of
--     type-variable positions `_↪_` into a center of n type variables
--     (GTSFImp's `_↪ᵗ_` with `keep`/`skip`) and their renaming `emb`;
--     the PERMISSION `permit` of a right rep. var and the DERIVED MARKS
--     `dmarks`; §2 the rep. var correspondence `RepRel` and its
--     renumberings; §3 `World`, `marksʷ`, `Paired` (ϱ = ϱᵍ ∪ ϱˡ),
--     `_+κ_`, and R1′/R2's condition `Unpermitted`/`LeftUnpermitted`/
--     `UnbindOK` (D28, D31); §4 the SLOTS and the index
--     `A ⊑ᵂ⟨ W ⟩[ O ] A′` (D31), with `A ⊑ᵂ⟨ W ⟩ A′` its O = [] case;
--     §5 the world operations `W ⊕²`, `W ⊕ᴸ`, `W ⊕ᴸ⇔ β` (claim-rep,
--     D29), `W ⊕ᴿ`, `W ⊕⁺^ β`, `W ⊕ʳ^ β`, `Join↪`/`Join1` (the join of
--     an opening by a left binder), the allocation renumberings, and
--     `underν²`; §6 the term-interior world `Interior W Θ Θ′ Wᵢ` and
--     conversion-context world `ConversionInterior W Θ Θ′ Wᶜ`, both
--     RELATIONS; §7 term-context imprecision `CtxImp`, `LiftCtx`,
--     `LiftCtxᴸ`; §8 well-formedness `WfWorld`, a SEPARATE predicate,
--     with payload imprecision `RepImp` (D23) and named uniqueness
--     `NamedUniqueᴸ`/`NamedUniqueᴿ` (D25); the well-formed openings
--     `SlotOK`/`SlotNe` and `JoinRep`, the rep. vars a boundary may
--     permit (D31; D32 adds `jr-rebind`, `Rebinds`); `Unjoins`,
--     `Dropped` and `Revoke`, the permissions a boundary may revoke for
--     its interior, paying with its exterior index (D32).
--   * REVOCATIONS (design.md D32, adopted 2026-10-09).  The dual of a
--     permission: a boundary that UNJOINS a type variable (one of a
--     joined pair is no longer bound inside) may drop its rep. var's
--     permission for its interior (`W ⇂κ κ₁`, κ₁ ⊆ κ), and pays with
--     its exterior index read without it.  Wrap's dual needs it; C5's
--     hidden variant stays dead because its right hide's exterior puts
--     X against ★.
--   * MARKS ARE COMPUTED, NOT STORED (design.md D28; Jeremy,
--     2026-10-05).  A world has a field `κʷ`, the PERMITTED right rep.
--     vars, and the mark of a center type variable is
--     `marksʷ W = dmarks (ηᴿʷ W) (κʷ W)`: a type variable the right
--     does not see (left-only) is X⊑★; a type variable the right sees is
--     X⊑★ iff its right rep. var is in κʷ, else X⊑X.  The center is a
--     number `Ωʷ` (nothing stores a mark).
--   * PERMISSIONS ARE CHOSEN AT JOINING BOUNDARIES (design.md D31,
--     adopted 2026-10-09; checked first as
--     proof/DGG/notes/D28pD30.agda).  κ changes ONLY at the boundary
--     rules of TermImprecision: a boundary may add, for its interior
--     only, the right rep. vars `K` of type variables it JOINS
--     (`JoinRep`: a matched fresh pair or a rejoin through ϱ, a rebind
--     (D32), or a new opening),
--     `Wᵢ +κ K = record Wᵢ { κʷ = K ++ κʷ Wᵢ }`, and it pays
--     with its interior index read at Wᵢ (without K).  D28's grants
--     at right checks are gone.
--   * OPENINGS ARE IN THE INDEX, NOT THE WORLD (design.md D31; history:
--     D26's openings, D27's pending list `πʷ`, both superseded).  The
--     index `A ⊑ᵂ⟨ W ⟩[ O ] A′` opens the left type's outer ∀s at the
--     SLOTS O (`OpenO`): `opn k` opens the next left ∀ at the right
--     type variable k, `skp` skips it (left-only, X⊑★, as type
--     imprecision's ∀⊑).  At O = [] it is
--     `marksʷ W ⊢ embᴸ W A ⊑ embᴿ W A′` definitionally, and that case
--     is written `A ⊑ᵂ⟨ W ⟩ A′`.  A world has no pending list.
--   * CLAIM-REP (design.md D29; Jeremy, 2026-10-06).  A left binder may
--     pair its abstract rep. var lexically with an UNNAMED right ★ rep.
--     var β (`W ⊕ᴸ⇔ β`): it is left-only (X⊑★) until a right boundary
--     names β, where `Interior.join-fresh` rejoins it (D25) and its mark
--     becomes β's permission (D28).
--   * ϱ IS ANY RELATION WHOSE PAIRS AGREE (design.md D25, revising
--     D13's "a right rep. var has at most one left partner").  What
--     the rejoin of `Interior` needs instead is NAMED UNIQUENESS: among
--     the rep. vars that a type variable denotes on one side, at most
--     one is paired with a given rep. var denoted on the other.  Unnamed
--     rep. vars are free, which admits C12 and L3d; allocations never
--     bind a type variable to a rep. var, so every evolution step
--     preserves it.
--   * DEFINITIONS ONLY.  Model: GTSFImp/proof/DGG/CtxImp.agda (`World`,
--     `ηᴸʷ`/`ηᴿʷ`, `impEnvʷ`, `_⊑ᵂ⟨_⟩_`, `CtxImp`), minus the stores,
--     `RebaseAt` and `ImpEnvMono` (no part of a world is ever rebased,
--     design.md §12.2).
--   * REPRESENTATION CHOICES.
--     - A world is indexed by the two type contexts `Δ` (left, more
--       precise) and `Δ′` (right).
--     - THE CENTER Ω IS A NUMBER `Ωʷ`; a center type variable is a
--       position below it.  The embeddings are indexed by `names Δ` and
--       by Ωʷ, so they cover every type variable in scope by
--       construction.  `emb` is the identity past the end (only
--       in-range positions are read).
--     - ϱ is two lists of pairs (left rep. var, right rep. var) over the
--       CURRENT de Bruijn rep. vars of the two sides: `ϱᵍʷ` (global,
--       store rep. vars) and `ϱˡʷ` (lexical, rep. vars bound by an
--       enclosing Λ, or by the join of an opening).  A binder or an
--       allocation renumbers the side it acts on; κʷ (right rep. vars)
--       is renumbered with the right side.
--     - `Interior` is declarative.  A continuing type variable (one
--       `toExt` sends to an exterior position) keeps its center
--       partner; a type variable the boundary itself introduces
--       (`Fresh`) joins the other side's type variable exactly when
--       their rep. vars are paired by ϱ (D25).  `Interior` keeps ϱ and
--       κ (`same-ϱᵍ`, `same-ϱˡ`, `same-κ`); the permissions a boundary
--       adds are the rule's `K`, on top of Wᵢ.
--   * PAYLOADS ARE COMPARED IN THE REPRESENTATION UNIVERSE (design.md
--     D23; Jeremy, 2026-10-03).  `Agree.rep-rep` relates two payloads
--     by `RepImp` (§8, `μ ⊢ R ⊑ᴿ⟨ W ⟩ R′`): free rep. vars correspond
--     through `Paired W`, local ∀-bound variables position-wise with
--     marks.
--   * R1′/R2's CONDITION (design.md D28, D31).  `Unpermitted W α`: the
--     LEFT rep. var α has no permitted right partner.  TermImprecision's
--     `⟪⟫⊑` takes `UnbindOK W A` for every left unbind of its boundary
--     (R1′: an unbind whose rep. var's type variable does not occur in
--     the boundary's exterior type A needs nothing, `ok-hidden`; else
--     R1, `ok-unbind`); ConversionImprecision's four ★ clauses take it
--     for the left type variable (`LeftUnpermitted`, R2).  They are
--     RULE premises, not WfWorld fields.
--   * DEVIATIONS from design.md §12.2 (each also in the report):
--     - `Interior` does not require `WfWorld Wᵢ`: WfWorld is kept
--       separate, and the boundary rules take it as a premise (of
--       `Wᵢ +κ K`).
--     - `W ⊕⁺^ β` (the premise world of the join of the opening of the
--       right entry `bind 0 β`, `join-⊕`) is its own operation: the
--       right side's new type variable is the boundary entry
--       `bind 0 β`, not a Λ, so the right context is
--       `reps Δ′ ∣ β ∷ names Δ′`, not `underΛ Δ′`; the lexical pair is
--       (0, β).
--     - `ConversionInterior`, like `Interior`, does not require
--       `WfWorld Wᶜ`.  A conversion context is the union of type
--       variables live anywhere along a boundary, so
--       continuation/freshness is stated by whether the type variable's
--       rep. var already has an exterior type variable, rather than by
--       `toExt` on the term-interior context.
--   * HISTORY (design.md §C12).  Before D26 the term relation had a
--     separate rule `∀⊑⟪+⟫`; D26 replaced it by the openings of `⊑⟪⟫`;
--     D27 stored them as a pending list `πʷ` in the world, popped by
--     `Open1`; D31 moved them into the index as slots and replaced
--     D28's grants by permissions chosen at joining boundaries.  Before
--     D28 the center was the mark list `μʷ` (D11, D15).

open import Data.Bool using (Bool; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.List using (List; []; _∷_; map; length; _++_)
open import Data.Nat using (_+_)
open import Data.Maybe using (just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Data.List.Relation.Unary.All using (All; [])
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
  using (Ty; `_; `ℕ; `𝔹; ★; _⇒_; `∀; Base; Renameᵗ; renameᵗ; ⇑ᵗ; extᵗ)
open import Ctx
open import Boundary using (Boundary; Change; bind; unbind;
  _⊢ⁱ_⇒_; _⊢ᶜ_⇒_; toExt; Fresh; InUnbinds; InBinds)
open import Imprecision
  using (VarImp; X⊑X; X⊑★; ImpEnv; extᵐ; instᵐ; _⊢_⊑_)
open import Coercion using (NonVar; NonStar; _∈ᵗ_; occurs)

private
  variable
    Δ Δ′ Δᵢ Δ′ᵢ Δᶜ Δ′ᶜ : Ctxᵗ

------------------------------------------------------------------------
-- 1. Embeddings of type-variable positions into the center; derived marks
------------------------------------------------------------------------

-- `η : names Δ ↪ n`: an order-preserving embedding of Δ's
-- type-variable positions into a center of n type variables (GTSFImp
-- `_↪ᵗ_`).  `keep` sends the next type variable to the next center type
-- variable; `skip` passes a center type variable this side does not
-- see.
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

-- a renumbering of the rep. vars the type variables denote moves no position
relabel : ∀ {η n} (f : RVar → RVar) → η ↪ n → map f η ↪ n
relabel f []↪      = []↪
relabel f (keep ι) = keep (relabel f ι)
relabel f (skip ι) = skip (relabel f ι)

-- THE PERMISSION of one right rep. var (design.md D28): X⊑★ when it is
-- in the permitted list, else X⊑X
permit : RVar → List RVar → VarImp
permit β []      = X⊑X
permit β (γ ∷ κ) = if β ≡ᵇ γ then X⊑★ else permit β κ

-- THE DERIVED MARKS: a center type variable the right sees has its right rep.
-- var's permission; a center type variable the right does not see (left-only)
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
    Ωʷ  : ℕ                     -- the center: how many center type variables
    ηᴸʷ : names Δ ↪ Ωʷ          -- the left names
    ηᴿʷ : names Δ′ ↪ Ωʷ         -- the right names
    ϱᵍʷ : RepRel                -- global: store rep. vars (D16)
    ϱˡʷ : RepRel                -- lexical: Λ- and boundary-bound (D16)
    κʷ  : List RVar             -- permitted right rep. vars (D28, D31)
open World public

-- THE MARKS of the center type variables, derived (design.md D28)
marksʷ : World Δ Δ′ → ImpEnv
marksʷ W = dmarks (ηᴿʷ W) (κʷ W)

-- ϱ = ϱᵍ ∪ ϱˡ
Paired : World Δ Δ′ → RVar → RVar → Set
Paired W α β = (ϱᵍʷ W ∋ᵨ α ⇔ β) ⊎ (ϱˡʷ W ∋ᵨ α ⇔ β)

-- a left and a right position denote the same center type variable
Joins : World Δ Δ′ → ℕ → ℕ → Set
Joins W X X′ = emb (ηᴸʷ W) X ≡ emb (ηᴿʷ W) X′

-- a world with no permission (κ = []; every top-level world, and most
-- literal worlds of the examples)
world⁰ : ∀ {Δ Δ′} (n : ℕ) → names Δ ↪ n → names Δ′ ↪ n
  → RepRel → RepRel → World Δ Δ′
world⁰ n η η′ ϱᵍ ϱˡ = world n η η′ ϱᵍ ϱˡ []

-- the closed world: no type variables, no rep. vars paired, no
-- permission
∅ʷ : World empty empty
∅ʷ = world⁰ 0 []↪ []↪ [] []

-- THE PERMISSIONS A BOUNDARY ADDS for its interior (design.md D31):
-- the only way κ grows.  `Wᵢ +κ []` is Wᵢ definitionally (record eta).
infixl 6 _+κ_
_+κ_ : World Δ Δ′ → List RVar → World Δ Δ′
W +κ K = record W { κʷ = K ++ κʷ W }

-- THE WORLD WITH ITS PERMISSIONS REPLACED (design.md D32): the premise
-- world of a boundary rule is `Wᵢ ⇂κ κ₁ +κ K`, where κ₁ is κʷ Wᵢ with
-- the REVOKED rep. vars removed (`Revoke`, §9).  `Wᵢ ⇂κ κʷ Wᵢ` is Wᵢ
-- definitionally (record eta), so a boundary that revokes nothing has
-- D31's premise world `Wᵢ +κ K`.
infixl 6 _⇂κ_
_⇂κ_ : World Δ Δ′ → List RVar → World Δ Δ′
W ⇂κ κ = record W { κʷ = κ }

-- R1/R2's CONDITION (design.md D28): the LEFT rep. var α has no
-- PERMITTED right partner (stated through `permit`, which the derived
-- marks read; equivalently ¬ ∃ β. Paired W α β × β ∈ κʷ W)
Unpermitted : World Δ Δ′ → RVar → Set
Unpermitted W α = ∀ {β} → Paired W α β → permit β (κʷ W) ≡ X⊑X

-- R2's form: the rep. var of the left type variable X (there is at most one)
LeftUnpermitted : World Δ Δ′ → ℕ → Set
LeftUnpermitted {Δ = Δ} W X = ∀ {α} → Δ ∋ᵗ X := α → Unpermitted W α

-- R1′'s form (design.md D31), per entry of a boundary with exterior
-- type A: a left UNBIND of α needs nothing when no type variable bound
-- to α occurs in A (`ok-hidden`: the boundary seals no α-value, it only
-- hides), else α unpermitted (`ok-unbind`, R1); a bind needs nothing
data UnbindOK (W : World Δ Δ′) (A : Ty) : Change → Set where
  ok-bind   : ∀ {X α} → UnbindOK W A (bind X α)
  ok-hidden : ∀ {Y α}
    → (∀ {X} → Δ ∋ᵗ X := α → occurs X A ≡ false)
    → UnbindOK W A (unbind Y α)
  ok-unbind : ∀ {Y α} → Unpermitted W α → UnbindOK W A (unbind Y α)

------------------------------------------------------------------------
-- 4. Type imprecision at a world (GTSFImp `_⊑ᵂ⟨_⟩_`)
------------------------------------------------------------------------

embᴸ : World Δ Δ′ → Ty → Ty
embᴸ W = renameᵗ (emb (ηᴸʷ W))

embᴿ : World Δ Δ′ → Ty → Ty
embᴿ W = renameᵗ (emb (ηᴿʷ W))

-- one opened binder in front of a renaming: the bound variable 0 goes
-- to the center type variable c
infixr 5 _⊳_
_⊳_ : ℕ → Renameᵗ → Renameᵗ
(c ⊳ ρ) zero    = c
(c ⊳ ρ) (suc X) = ρ X

-- A SLOT of the index (design.md D31): open the next left ∀ at the
-- right type variable k (a position of the right context), or SKIP it:
-- the left ∀ waits, left-only at X⊑★ (as type imprecision's ∀⊑)
data Slot : Set where
  opn : ℕ → Slot
  skp : Slot

-- `OpenO μ e O ρ A B`: A with its outer ∀s opened at the slots O
-- (outermost first; e embeds right positions into center type
-- variables), renamed by ρ, is below B.  A skip adds a left-only center
-- type variable, as `∀⊑` does (with its side conditions).  A non-∀ type
-- under a slot has no index.
OpenO : ImpEnv → (ℕ → ℕ) → List Slot → Renameᵗ → Ty → Ty → Set
OpenO μ e []          ρ A        B = μ ⊢ renameᵗ ρ A ⊑ B
OpenO μ e (opn k ∷ O) ρ (`∀ A)   B = OpenO μ e O (e k ⊳ ρ) A B
OpenO μ e (skp ∷ O)   ρ (`∀ A)   B =
  NonVar A × 0 ∈ᵗ A
  × OpenO (instᵐ μ) (λ k → suc (e k)) O (extᵗ ρ) A (⇑ᵗ B)
OpenO μ e (_ ∷ _)     ρ (` X)    B = ⊥
OpenO μ e (_ ∷ _)     ρ `ℕ       B = ⊥
OpenO μ e (_ ∷ _)     ρ `𝔹       B = ⊥
OpenO μ e (_ ∷ _)     ρ ★        B = ⊥
OpenO μ e (_ ∷ _)     ρ (A ⇒ A′) B = ⊥

-- THE INDEX of the term relation, `A ⊑_W^O A′` (design.md §9, D31): the
-- actual left type opened at the slots O, at the derived marks (D28)
infix 4 _⊑ᵂ⟨_⟩[_]_ _⊑ᵂ⟨_⟩_
_⊑ᵂ⟨_⟩[_]_ : Ty → World Δ Δ′ → List Slot → Ty → Set
A ⊑ᵂ⟨ W ⟩[ O ] A′ =
  OpenO (marksʷ W) (emb (ηᴿʷ W)) O (emb (ηᴸʷ W)) A (embᴿ W A′)

-- ... with no slot, `A ⊑_W A′`: `marksʷ W ⊢ embᴸ W A ⊑ embᴿ W A′`,
-- definitionally
_⊑ᵂ⟨_⟩_ : Ty → World Δ Δ′ → Ty → Set
A ⊑ᵂ⟨ W ⟩ A′ = A ⊑ᵂ⟨ W ⟩[ [] ] A′

------------------------------------------------------------------------
-- 5. World operations (design.md §12.2)
------------------------------------------------------------------------

-- No operation takes a mark (they are derived, D28).  A new RIGHT rep.
-- var (a right Λ, a right allocation) renumbers κ (`map suc`); a
-- boundary entry binds no new rep. var and leaves κ alone.  A world has
-- no openings (they are slots of the index, D31), so a new right type
-- variable moves nothing else.

-- W ⊕² — both sides bind X by a Λ: a new center type variable in both
-- images, and the two abstract rep. vars paired lexically; the new
-- right rep. var 0 is not permitted, so X is X⊑X
infixl 6 _⊕² _⊕ᴸ _⊕ᴸ⇔_ _⊕ᴿ _⊕⁺^_ _⊕ʳ^_
_⊕² : World Δ Δ′ → World (underΛ Δ) (underΛ Δ′)
world n η η′ ϱᵍ ϱˡ κ ⊕² =
  world (suc n) (keep (relabel suc η)) (keep (relabel suc η′))
        (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ) (map suc κ)

-- W ⊕ᴸ — the left side alone binds X: in η's image only (so X⊑★);
-- its abstract rep. var is unpaired
_⊕ᴸ : World Δ Δ′ → World (underΛ Δ) Δ′
world n η η′ ϱᵍ ϱˡ κ ⊕ᴸ =
  world (suc n) (keep (relabel suc η)) (skip η′)
        (shiftᴸ ϱᵍ) (shiftᴸ ϱˡ) κ

-- W ⊕ᴸ⇔ β — CLAIM-REP (design.md D29): the left side alone binds X, as
-- `W ⊕ᴸ` (in η's image only, so X⊑★ while no right type variable joins
-- it), and its abstract rep. var is paired LEXICALLY with the right rep.
-- var β, to which no right type variable in scope is bound yet.  A
-- right boundary that later binds a type variable to β (`+X^β`)
-- REJOINS the binder by `Interior.join-fresh` (D25); from there X's
-- mark is β's permission (`dmarks`, D28), X⊑X unless a joining
-- boundary permits β (D31).  κ is unchanged (no right rep. var moves).
_⊕ᴸ⇔_ : World Δ Δ′ → RVar → World (underΛ Δ) Δ′
world n η η′ ϱᵍ ϱˡ κ ⊕ᴸ⇔ β =
  world (suc n) (keep (relabel suc η)) (skip η′)
        (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) κ

-- W ⊕ᴿ — the right side alone binds X: in η′'s image only (used by
-- no rule; recorded for completeness)
_⊕ᴿ : World Δ Δ′ → World Δ (underΛ Δ′)
world n η η′ ϱᵍ ϱˡ κ ⊕ᴿ =
  world (suc n) (skip η) (keep (relabel suc η′))
        (shiftᴿ ϱᵍ) (shiftᴿ ϱˡ) (map suc κ)

-- the premise world of the join of the opening of `bind 0 β`
-- (`join-⊕`): the left goes under its binder, a Λ-like binder (an
-- abstract rep. var at 0), the right is inside its boundary `bind 0 β`;
-- one new center type variable, and the left abstract rep. var is
-- paired lexically with β (design.md §12.2, D16)
_⊕⁺^_ : World Δ Δ′ → (β : RVar)
  → World (underΛ Δ) (reps Δ′ ∣ (β ∷ names Δ′))
world n η η′ ϱᵍ ϱˡ κ ⊕⁺^ β =
  world (suc n) (keep (relabel suc η)) (keep η′)
        (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) κ

-- the interior world of `⊑⟪⟫` at a single right entry `bind 0 β`
-- (`+X^β`): X is a right-only type variable (FixB's `_⊕ʳ_^_`)
_⊕ʳ^_ : World Δ Δ′ → (β : RVar) → World Δ (reps Δ′ ∣ (β ∷ names Δ′))
world n η η′ ϱᵍ ϱˡ κ ⊕ʳ^ β =
  world (suc n) (skip η) (keep η′) ϱᵍ ϱˡ κ

-- JOINS (design.md D31; history: D26's openings, D27's pops).  A left
-- binder (`Λ⊑`) may join the right-only type variable k of the next
-- opening of the index: the binder (a Λ-like abstract rep. var at 0, as
-- `underΛ`) joins k's center type variable.  `Join↪ ι ι′ ι⁺ k`: the
-- left's NEW type variable 0 is kept into the center type variable of
-- the right's k, which is RIGHT-ONLY; the center type variables before
-- it are right-only too (the left skips them), so the left's order is
-- preserved.  `ι⁺` is the left embedding after the join (FixB's
-- `JoinΛ`, at any position k).
data Join↪ {η : TyCtx}
    : ∀ {η′ n} → η ↪ n → η′ ↪ n → (zero ∷ map suc η) ↪ n → ℕ → Set where
  join-here : ∀ {β η′ n} {ι : η ↪ n} {ι′ : η′ ↪ n}
    → Join↪ (skip ι) (keep {α = β} ι′) (keep (relabel suc ι)) zero
  join-there : ∀ {β η′ n k} {ι : η ↪ n} {ι′ : η′ ↪ n}
      {ι⁺ : (zero ∷ map suc η) ↪ n}
    → Join↪ ι ι′ ι⁺ k
    → Join↪ (skip ι) (keep {α = β} ι′) (skip ι⁺) (suc k)

-- `Join1 W k W₁`: the join of the opening k, whose rep. var β is bound
-- to ★; the left abstract rep. var is paired with β LEXICALLY (D16).
-- The right does not move, so κ is unchanged.  `W ⊕⁺^ β` is the join
-- of type variable 0 of `W ⊕ʳ^ β` (`join-⊕`).
data Join1 {Δ Δ′ : Ctxᵗ} : World Δ Δ′ → ℕ → World (underΛ Δ) Δ′ → Set where
  join1 : ∀ {n ϱᵍ ϱˡ κ k β} {ι : names Δ ↪ n} {ι′ : names Δ′ ↪ n}
      {ι⁺ : names (underΛ Δ) ↪ n}
    → Join↪ ι ι′ ι⁺ k
    → Δ′ ∋ᵗ k := β
    → Δ′ ∋rep β := ★
    → Join1 (world n ι ι′ ϱᵍ ϱˡ κ) k
            (world n ι⁺ ι′ (shiftᴸ ϱᵍ) ((zero , β) ∷ shiftᴸ ϱˡ) κ)

join-⊕ : ∀ {W : World Δ Δ′} {β}
  → Δ′ ∋rep β := ★
  → Join1 (W ⊕ʳ^ β) 0 (W ⊕⁺^ β)
join-⊕ hβ = join1 join-here here hβ

-- Renumbering on allocation (for the metatheory; no rule reads a world
-- under an allocation).  An unmatched allocation only renumbers its own
-- side (κ with the right side); a matched pair of TyBetas adds (0, 0)
-- to ϱᵍ; a left TyBeta catching up with a right boundary `bind 0 β`
-- whose type variable a left binder joined adds (0, β) (design.md
-- §12.2, D16).
allocᴸ : (R : Ty) → World Δ Δ′ → World (allocate R Δ) Δ′
allocᴸ R (world n η η′ ϱᵍ ϱˡ κ) =
  world n (relabel suc η) η′ (shiftᴸ ϱᵍ) (shiftᴸ ϱˡ) κ

allocᴿ : (R′ : Ty) → World Δ Δ′ → World Δ (allocate R′ Δ′)
allocᴿ R′ (world n η η′ ϱᵍ ϱˡ κ) =
  world n η (relabel suc η′) (shiftᴿ ϱᵍ) (shiftᴿ ϱˡ) (map suc κ)

alloc² : (R R′ : Ty) → World Δ Δ′
  → World (allocate R Δ) (allocate R′ Δ′)
alloc² R R′ (world n η η′ ϱᵍ ϱˡ κ) =
  world n (relabel suc η) (relabel suc η′)
        ((zero , zero) ∷ shift² ϱᵍ) (shift² ϱˡ) (map suc κ)

-- The two ν-bound rep. vars are in scope only while their conversions
-- are compared.  Unlike `alloc²`, which records matched runtime
-- allocations globally, this operation records (0, 0) lexically.
underν² : (R R′ : Ty) → World Δ Δ′
  → World (allocate R Δ) (allocate R′ Δ′)
underν² R R′ (world n η η′ ϱᵍ ϱˡ κ) =
  world n (relabel suc η) (relabel suc η′)
        (shift² ϱᵍ) ((zero , zero) ∷ shift² ϱˡ) (map suc κ)

allocᴸ⇔ : (R : Ty) (β : RVar) → World Δ Δ′ → World (allocate R Δ) Δ′
allocᴸ⇔ R β (world n η η′ ϱᵍ ϱˡ κ) =
  world n (relabel suc η) η′ ((zero , β) ∷ shiftᴸ ϱᵍ) (shiftᴸ ϱˡ) κ

------------------------------------------------------------------------
-- 6. The interior world W[δ ∥ δ′] (a relation; design.md §12.2)
------------------------------------------------------------------------

-- `Interior W Θ Θ′ Wᵢ`: Wᵢ is an interior world of the boundary pair
-- `[Θ] ⊑ [Θ′]` in W.  A one-sided boundary is the case Θ = [] or
-- Θ′ = [] (W[δ ∥ ·], W[· ∥ δ′]); `toExt [] X = just X`, so every type variable
-- of the side without a boundary continues.  There are no mark fields:
-- the marks are derived from the joins and κ, which a boundary keeps
-- (design.md D28; D11's choice and D15's keep-on-rejoin are gone).
record Interior (W : World Δ Δ′) (Θ Θ′ : Boundary)
    (Wᵢ : World Δᵢ Δ′ᵢ) : Set where
  constructor interior-world
  field
    -- each side's changes act on that side's type variables
    int-left  : Δ ⊢ⁱ Θ ⇒ Δᵢ
    int-right : Δ′ ⊢ⁱ Θ′ ⇒ Δ′ᵢ
    -- a boundary relates no new rep. vars
    same-ϱᵍ : ϱᵍʷ Wᵢ ≡ ϱᵍʷ W
    same-ϱˡ : ϱˡʷ Wᵢ ≡ ϱˡʷ W
    -- a boundary moves no rep. var: the permissions pass through (D28);
    -- the rule may add its own `K` on top (`_+κ_`, D31)
    same-κ  : κʷ Wᵢ ≡ κʷ W
    -- two continuing type variables share a center type variable
    -- inside iff outside
    join-cont : ∀ {X X′ Xₑ X′ₑ}
      → Δᵢ ∋tv X → Δ′ᵢ ∋tv X′
      → toExt Θ X ≡ just Xₑ → toExt Θ′ X′ ≡ just X′ₑ
      → (Joins Wᵢ X X′ → Joins W Xₑ X′ₑ)
        × (Joins W Xₑ X′ₑ → Joins Wᵢ X X′)
    -- a type variable the boundary introduces joins exactly the other side's
    -- type variable of a paired rep. var (D25: a right `+X^β` rejoins the left
    -- partner of β whose type variable is in scope; `wf-namedᴸ` of Wᵢ makes it
    -- unique); otherwise it is one-sided
    join-fresh : ∀ {X X′ α β}
      → Δᵢ ∋ᵗ X := α → Δ′ᵢ ∋ᵗ X′ := β
      → Fresh Θ X ⊎ Fresh Θ′ X′
      → (Joins Wᵢ X X′ → Paired W α β)
        × (Paired W α β → Joins Wᵢ X X′)
open Interior public

-- `ConversionInterior W Θ Θ′ Wᶜ`: Wᶜ relates the two contexts in
-- which the boundary conversions are read.  Those contexts keep every
-- exterior type variable and add one for each newly encountered rep. var;
-- an unbind never removes a conversion-context type variable.  Consequently a
-- type variable continues exactly when its rep. var already has an exterior
-- type variable, and it is fresh exactly when that rep. var has none.
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

-- An entry reads the marks, the center and the two embeddings (not ϱ).
-- The marks are a parameter of their own (they are derived from ηᴿ and
-- κ).  Only the term-closed interior of a boundary is read at a larger
-- κ (`_+κ_`, D31), so no rule moves a nonempty term context to new
-- marks.
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

-- the entries are read at the derived marks
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
-- is any world over `underΛ Δ` (`W ⊕ᴸ` for a fresh left-only binder,
-- `W ⊕ᴸ⇔ β` for claim-rep, or the `Join1` of an opening, design.md D31)
data LiftCtxᴸ {ns ns′ n μ ns₁ n₁ μ₁} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {ηᴸ₁ : ns₁ ↪ n₁} {ηᴿ₁ : ns′ ↪ n₁}
    : Entries μ ηᴸ ηᴿ → Entries μ₁ ηᴸ₁ ηᴿ₁ → Set where
  liftᴸ-[] : LiftCtxᴸ [] []
  liftᴸ-∷  : ∀ {γ γ′ A A′ p p′} → LiftCtxᴸ γ γ′
    → LiftCtxᴸ (ctx-imp A A′ p ∷ γ) (ctx-imp (⇑ᵗ A) A′ p′ ∷ γ′)

------------------------------------------------------------------------
-- 8. Well-formedness (design.md §12.2), a SEPARATE predicate
------------------------------------------------------------------------

-- The two embeddings jointly: every center type variable is in at least one
-- image (no skip/skip); a type variable in both images denotes paired rep.
-- vars.  No marks: a left-only type variable is
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
-- a rep. var carries no mark; marks belong to type variables, D12).
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
-- several partners on either side; but among the rep. vars to which a
-- type variable of one side is bound, at most one is paired with a
-- given rep. var bound on the other side.  This is what `Interior`'s
-- rejoin reads: a type variable a boundary introduces must join every
-- other-side type variable in scope whose rep. var is paired with its
-- own, and an embedding joins one to at most one other.  Rep. vars with
-- no type variable in scope (store rep. vars, rep. vars hidden by an
-- unbind) are unconstrained.
NamedUniqueᴸ : World Δ Δ′ → Set
NamedUniqueᴸ {Δ} {Δ′} W = ∀ {α α′ β}
  → names Δ ∋ᵅ α → names Δ ∋ᵅ α′ → names Δ′ ∋ᵅ β
  → Paired W α β → Paired W α′ β → α ≡ α′

NamedUniqueᴿ : World Δ Δ′ → Set
NamedUniqueᴿ {Δ} {Δ′} W = ∀ {α β β′}
  → names Δ ∋ᵅ α → names Δ′ ∋ᵅ β → names Δ′ ∋ᵅ β′
  → Paired W α β → Paired W α β′ → β ≡ β′

-- β has no left partner to which a type variable of Δ is bound (D25's
-- scoped analogue of D13's `NoLeftPartner`; an opening's rep. var)
NoNamedPartner : World Δ Δ′ → RVar → Set
NoNamedPartner {Δ} W β = ∀ {α} → names Δ ∋ᵅ α → ¬ Paired W α β

-- a right type variable that no left type variable joins
RightOnly : World Δ Δ′ → ℕ → Set
RightOnly {Δ = Δ} W k = ∀ {X} → Δ ∋tv X → ¬ Joins W X k

record WfWorld (W : World Δ Δ′) : Set where
  constructor wf-world
  field
    wf-joint : Joint (Paired W) (ηᴸʷ W) (ηᴿʷ W)
    wf-agree : ∀ {α β} → Paired W α β → Agree W α β
    -- D25 (replaces D13's one-left-partner rule): named uniqueness
    wf-namedᴸ : NamedUniqueᴸ W
    wf-namedᴿ : NamedUniqueᴿ W
    -- D28: every permitted rep. var is a right rep. var (bound to a
    -- type variable or not: a right hide keeps its permission, P4 B4)
    wf-permits  : All (reps Δ′ ∋ʳ_) (κʷ W)
open WfWorld public

------------------------------------------------------------------------
-- 9. Openings and permissions at a boundary (design.md D31)
------------------------------------------------------------------------

-- AN OPENING IS WELL FORMED (checked where `⊑⟪⟫` creates or carries
-- it): its type variable k is bound to a ★ rep. var β, right-only, and
-- β has no left partner to which a type variable is bound (so the join
-- keeps named uniqueness, as `wf-⊕⁺`).  Its mark is derived (D28):
-- X⊑★ exactly when β is permitted.
OpeningOK : World Δ Δ′ → ℕ → Set
OpeningOK {Δ′ = Δ′} W k =
  Σ[ β ∈ RVar ] (Δ′ ∋ᵗ k := β) × (Δ′ ∋rep β := ★) × RightOnly W k
    × NoNamedPartner W β

SlotOK : World Δ Δ′ → Slot → Set
SlotOK W (opn k) = OpeningOK W k
SlotOK W skp     = ⊤

-- the opened type variables are distinct
SlotNe : Slot → Slot → Set
SlotNe (opn k) (opn k′) = k ≢ k′
SlotNe (opn k) skp      = ⊤
SlotNe skp     _        = ⊤

-- k is opened by one of the slots N (the NEW slots of a `⊑⟪⟫`)
infix 4 _∋ᵒ_
data _∋ᵒ_ : List Slot → ℕ → Set where
  oh : ∀ {k N} → (opn k ∷ N) ∋ᵒ k
  ot : ∀ {s k N} → N ∋ᵒ k → (s ∷ N) ∋ᵒ k

-- `Rebinds Θ α`: an entry of Θ unbinds α and a later entry binds it
-- again (the merged `[−X, +X]` of a hide over a rejoin, design.md D32);
-- with a type variable bound to α inside, that type variable CONTINUES
-- (`toExt` finds the unbind through `seekUnbind`), so it is not `Fresh`
Rebinds : Boundary → RVar → Set
Rebinds Θ α = InUnbinds α Θ × InBinds α Θ

-- `JoinRep Wᵢ Θ Θ′ N β`: the boundary pair `[Θ] ⊑ [Θ′]` with new slots
-- N JOINS a type variable bound to the right rep. var β, so it may
-- permit β for its interior (design.md D31, "K ⊆ joined"): inside, a
-- left type variable is joined to a right one bound to β, and one of
-- the two is introduced by this boundary (a matched fresh pair, or a
-- rejoin through ϱ), or REBOUND by it (D32: an entry unbinds its rep.
-- var and a later entry binds it again, so a Merge of a hide over a
-- rejoin keeps the rejoin's permission); or β's type variable is a new
-- opening
data JoinRep {Δᵢ Δ′ᵢ : Ctxᵗ} (Wᵢ : World Δᵢ Δ′ᵢ) (Θ Θ′ : Boundary)
    (N : List Slot) (β : RVar) : Set where
  jr-join : ∀ {X X′}
    → Δᵢ ∋tv X → Δ′ᵢ ∋ᵗ X′ := β
    → Fresh Θ X ⊎ Fresh Θ′ X′
    → Joins Wᵢ X X′
    → JoinRep Wᵢ Θ Θ′ N β
  jr-rebind : ∀ {X X′}
    → Δᵢ ∋tv X → Δ′ᵢ ∋ᵗ X′ := β
    → (Σ[ α ∈ RVar ] (Δᵢ ∋ᵗ X := α) × Rebinds Θ α) ⊎ Rebinds Θ′ β
    → Joins Wᵢ X X′
    → JoinRep Wᵢ Θ Θ′ N β
  jr-open : ∀ {k} → N ∋ᵒ k → Δ′ᵢ ∋ᵗ k := β → JoinRep Wᵢ Θ Θ′ N β

-- THE REVOCATIONS OF A BOUNDARY (design.md D32, the dual of D31's
-- permissions).  `Unjoins W Wᵢ β`: outside, a left type variable is
-- joined to a right one bound to β, and inside one of the two rep.
-- vars is no longer bound to a type variable: the boundary UNJOINS
-- them (a hide, a seal, or the dual a Wrap puts on its argument).
data Unjoins {Δ Δ′ Δᵢ Δ′ᵢ : Ctxᵗ} (W : World Δ Δ′) (Wᵢ : World Δᵢ Δ′ᵢ)
    (β : RVar) : Set where
  unjoin : ∀ {X X′ α}
    → Δ ∋ᵗ X := α → Δ′ ∋ᵗ X′ := β
    → Joins W X X′
    → ¬ (names Δᵢ ∋ᵅ α) ⊎ ¬ (names Δ′ᵢ ∋ᵅ β)
    → Unjoins W Wᵢ β

-- `Dropped P κ κ₁`: κ₁ is κ with some entries satisfying P removed
data Dropped (P : RVar → Set) : List RVar → List RVar → Set where
  dr-[]   : Dropped P [] []
  dr-keep : ∀ {β κ κ₁} → Dropped P κ κ₁ → Dropped P (β ∷ κ) (β ∷ κ₁)
  dr-drop : ∀ {β κ κ₁} → P β → Dropped P κ κ₁ → Dropped P (β ∷ κ) κ₁

-- `Revoke W Wᵢ O A A′ κ₁`: the boundary with exterior index
-- `A ⊑_W^O A′` and interior world Wᵢ reads its interior at the
-- permissions κ₁: all of κʷ Wᵢ (`rv-none`), or κʷ Wᵢ without some
-- rep. vars it UNJOINS, and then it PAYS with its exterior index read
-- without them (`rv-drop`, "the unjoin pays").  The payment keeps
-- C5's hidden variant dead: a right hide whose exterior puts the left's
-- X against ★ needs X's permission outside, so it cannot revoke it.
data Revoke {Δ Δ′ Δᵢ Δ′ᵢ : Ctxᵗ} (W : World Δ Δ′) (Wᵢ : World Δᵢ Δ′ᵢ)
    (O : List Slot) (A A′ : Ty) : List RVar → Set where
  rv-none : Revoke W Wᵢ O A A′ (κʷ Wᵢ)
  rv-drop : ∀ {κ₁}
    → Dropped (Unjoins W Wᵢ) (κʷ Wᵢ) κ₁
    → A ⊑ᵂ⟨ W ⇂κ κ₁ ⟩[ O ] A′
    → Revoke W Wᵢ O A A′ κ₁
