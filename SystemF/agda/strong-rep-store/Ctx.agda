module strong-rep-store.Ctx where

-- File Charter:
--   * THE TWO DE BRUIJN UNIVERSES AND EVERY RELATION OVER THEM.  §1
--     declares `RVar`, `RepBinding` (`abstR`/`bindR`), `RepCtx`,
--     `TyCtx` and the pair `Ctxᵗ = reps ∣ names`.  §2 is the lookup
--     family — `_∋ˡ_:=_`, `_∋ᵗ_:=_`, `_∋tv_`, `_∋ʳ_:=_`, `_∋rep_:=_`,
--     `_∋_:=ᴿ_`, `_∋ʳ_`, `_∋ᵅ_`, `_⊆ᵃ_`.  §3 is ordinary type
--     formation `_⊢ᵗ_` with `underΛ` and `Base`; §4 representation
--     payloads `_⊢ref[_]_`, `_⊢ᴿ[_]_`, `WfRepCtx`; §5 the two readings
--     of `Ty` — `_⊢_~_`, `_⊢ᶜ_~_`, `_⊢_≈_⊣_`, `SameTyExt`, `shiftRep`
--     and the lookup square `_∋_:=_`; §6 well-formedness `_∌ʳ_`,
--     `Unique`, `ValidNames`, `WfCtx`.  §§8–11 are the representation
--     universe's machinery: `extN`/`Injᵗ`, `shiftBy`/`pushRepBinds`/
--     `extendReps`/`_⊢ᴮ_`, the insert/delete relations
--     `_⊢+_at_⇒_`/`_⊢-_at_⇒_`, and the renaming interface `RepWk`.
--   * DEFINITIONS ONLY.  Every lemma about the above lives in
--     strong-rep-store.proof.Ctx (notes/DECISIONS.md, 2026-09-20).  Anything
--     mentioning `Change` or `Boundary` — the boundary scope, its two induced
--     contexts, `BoundaryWf` — is strong-rep-store.Boundary; terms and the typing
--     judgement are strong-rep-store.Terms; conversions are
-- strong-rep-store.Conversion.
--   * TWO INVARIANTS BEFORE TOUCHING ANYTHING HERE.  (1) `names Γ`
--     holds EXACTLY the ordinary type variables currently in scope, and
--     an entry is the representation variable named at that position —
--     so a CONCEALED ordinary variable has no entry at all, and a
--     represented payload's free indices live in the OTHER universe.
--     (2) A representation-only renaming leaves every ordinary POSITION
--     where it was (§8, §11): it renames `reps` and acts on the name
--     map by `map ρ`, so no ordinary spelling in any type, conversion
--     or change moves.  `RepWk` is exactly what such a move must
--     supply — three fields for `WfCtx`'s three obligations one
--     universe down, plus injectivity, which is what a `lock`'s
--     freshness record needs — and it is what makes `renᴹᴿ`
--     (strong-rep-store.TermSubst) type-preserving.
--
-- The two uses of the old type-variable slots are split into distinct de
-- Bruijn universes:
--
--   * `names Γ` contains exactly the ordinary type variables currently in
--     scope. An entry is the representation variable named by that ordinary
--     variable. A concealed ordinary variable has no entry here.
--
--   * `reps Γ` contains abstract and represented representation variables.
--     A represented payload is a `Ty` whose FREE indices range over this
--     representation-variable universe. A `∀` inside the payload binds an
--     ordinary local type variable in the usual way.
--
-- A term-level `Λ` extends both universes: it binds an abstract representation
-- variable and an ordinary type variable that names it. Boundary scopes
-- extend the representation universe and change the ordinary name map; those
-- operations live in strong-rep-store.Boundary.

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (_×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import strong-rep-store.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; Renameᵗ; renameᵗ; extᵗ; ⇑ᵗ)

------------------------------------------------------------------------
-- 1. The two de Bruijn universes
------------------------------------------------------------------------

RVar : Set
RVar = ℕ

data RepBinding : Set where
  abstR : RepBinding
  bindR : Ty → RepBinding

RepCtx : Set
RepCtx = List RepBinding

TyCtx : Set
TyCtx = List RVar

record Ctxᵗ : Set where
  constructor _∣_
  field
    reps  : RepCtx
    names : TyCtx
open Ctxᵗ public

-- View one context's ordinary names after a representation renaming, using a
-- second context's representation store.  Crossings use this when the same
-- ordinary spelling is carried across an inserted representation binder: the
-- positions stay fixed, but the representation indices they denote move.
renNameCtx : Renameᵗ → Ctxᵗ → Ctxᵗ → Ctxᵗ
renNameCtx ρ target source = reps target ∣ map ρ (names source)

private
  variable
    Γ Γ′ : Ctxᵗ
    Ξ : RepCtx
    Δ Δ′ η : TyCtx
    Rs : List Ty
    A B R S : Ty
    b b′ : RepBinding
    X Y i n : ℕ
    α β : RVar

------------------------------------------------------------------------
-- 2. Lookup
------------------------------------------------------------------------

infix 4 _∋ˡ_:=_
data _∋ˡ_:=_ {A : Set} : List A → ℕ → A → Set where
  here  : ∀ {x xs} → (x ∷ xs) ∋ˡ zero := x
  there : ∀ {x y xs i} → xs ∋ˡ i := x → (y ∷ xs) ∋ˡ suc i := x

-- An ordinary type variable names a representation variable.
infix 4 _∋ᵗ_:=_
_∋ᵗ_:=_ : Ctxᵗ → ℕ → RVar → Set
Γ ∋ᵗ X := α = names Γ ∋ˡ X := α

infix 4 _∋tv_
_∋tv_ : Ctxᵗ → ℕ → Set
Γ ∋tv X = ∃[ α ] Γ ∋ᵗ X := α

renRepBinding : Renameᵗ → RepBinding → RepBinding
renRepBinding ρ abstR     = abstR
renRepBinding ρ (bindR R) = bindR (renameᵗ ρ R)

-- A representation payload is stored outside its own binder. Looking it up
-- shifts it through that binder and every newer representation binder.
infix 4 _∋ʳ_:=_
data _∋ʳ_:=_ : RepCtx → RVar → RepBinding → Set where
  r-here  : (b ∷ Ξ) ∋ʳ zero := renRepBinding suc b
  r-there : Ξ ∋ʳ α := b
    → (bindR R ∷ Ξ) ∋ʳ suc α := renRepBinding suc b
  r-there-abst : Ξ ∋ʳ α := b
    → (abstR ∷ Ξ) ∋ʳ suc α := renRepBinding suc b

infix 4 _∋rep_:=_
_∋rep_:=_ : Ctxᵗ → RVar → Ty → Set
Γ ∋rep α := R = reps Γ ∋ʳ α := bindR R

-- The composite lookup used by conversions: ordinary X names α, whose
-- representation is R.
infix 4 _∋_:=ᴿ_
_∋_:=ᴿ_ : Ctxᵗ → ℕ → Ty → Set
Γ ∋ X :=ᴿ R = ∃[ α ] ((Γ ∋ᵗ X := α) × (Γ ∋rep α := R))

infix 4 _∋ʳ_
_∋ʳ_ : RepCtx → RVar → Set
Ξ ∋ʳ α = ∃[ b ] Ξ ∋ˡ α := b

-- `Δ ∋ᵅ α`: α has an ordinary name in Δ.
infix 4 _∋ᵅ_
_∋ᵅ_ : TyCtx → RVar → Set
Δ ∋ᵅ α = ∃[ X ] Δ ∋ˡ X := α

infix 4 _⊆ᵃ_
_⊆ᵃ_ : TyCtx → TyCtx → Set
Δ ⊆ᵃ Δ′ = ∀ {α} → Δ ∋ᵅ α → Δ′ ∋ᵅ α

------------------------------------------------------------------------
-- 3. Ordinary types
------------------------------------------------------------------------

shiftNames : TyCtx → TyCtx
shiftNames = map suc

-- A term-level `Λ` and the premise of ordinary `∀` formation bind both an
-- ordinary type variable and an abstract representation variable.
underΛ : Ctxᵗ → Ctxᵗ
underΛ (Ξ ∣ Δ) = (abstR ∷ Ξ) ∣ (zero ∷ shiftNames Δ)

infix 4 _⊢ᵗ_
data _⊢ᵗ_ : Ctxᵗ → Ty → Set where
  wf-var : Γ ∋tv X → Γ ⊢ᵗ ` X
  wf-ℕ   : Γ ⊢ᵗ `ℕ
  wf-𝔹   : Γ ⊢ᵗ `𝔹
  wf-⇒   : Γ ⊢ᵗ A → Γ ⊢ᵗ B → Γ ⊢ᵗ A ⇒ B
  wf-∀   : underΛ Γ ⊢ᵗ A → Γ ⊢ᵗ `∀ A

data Base : Ty → Set where
  base-ℕ : Base `ℕ
  base-𝔹 : Base `𝔹

------------------------------------------------------------------------
-- 4. Representation payloads
------------------------------------------------------------------------

-- A payload has a mixed de Bruijn interpretation. The first `n` indices are
-- ordinary variables bound by enclosing payload `∀`s. Index `n + α` is the
-- free representation variable α.
infix 4 _⊢ref[_]_
data _⊢ref[_]_ (Ξ : RepCtx) (n : ℕ) : ℕ → Set where
  local-ref : i < n → Ξ ⊢ref[ n ] i
  free-ref  : Ξ ∋ˡ α := b → Ξ ⊢ref[ n ] (n + α)

infix 4 _⊢ᴿ[_]_
data _⊢ᴿ[_]_ (Ξ : RepCtx) (n : ℕ) : Ty → Set where
  wfᴿ-var : Ξ ⊢ref[ n ] i → Ξ ⊢ᴿ[ n ] ` i
  wfᴿ-ℕ   : Ξ ⊢ᴿ[ n ] `ℕ
  wfᴿ-𝔹   : Ξ ⊢ᴿ[ n ] `𝔹
  wfᴿ-⇒   : Ξ ⊢ᴿ[ n ] R → Ξ ⊢ᴿ[ n ] S → Ξ ⊢ᴿ[ n ] R ⇒ S
  wfᴿ-∀   : Ξ ⊢ᴿ[ suc n ] R → Ξ ⊢ᴿ[ n ] `∀ R

infix 4 _⊢ᴿ_
_⊢ᴿ_ : RepCtx → Ty → Set
Ξ ⊢ᴿ R = Ξ ⊢ᴿ[ zero ] R

-- A concrete representation is checked outside its own binder.
data WfRepCtx : RepCtx → Set where
  wf-reps[] : WfRepCtx []
  wf-abstR  : WfRepCtx Ξ → WfRepCtx (abstR ∷ Ξ)
  wf-bindR  : Ξ ⊢ᴿ R → WfRepCtx Ξ → WfRepCtx (bindR R ∷ Ξ)

------------------------------------------------------------------------
-- 5. Relating the two readings of `Ty`
------------------------------------------------------------------------

-- Free ordinary variables are translated through the name map. A `∀`
-- extends only the LOCAL binder prefix on both sides; it does not allocate a
-- free representation variable.
infix 4 _⊢_~_
data _⊢_~_ (η : TyCtx) : Ty → Ty → Set where
  same-var : η ∋ˡ X := α → η ⊢ ` X ~ ` α
  same-ℕ   : η ⊢ `ℕ ~ `ℕ
  same-𝔹   : η ⊢ `𝔹 ~ `𝔹
  same-⇒   : η ⊢ A ~ R → η ⊢ B ~ S → η ⊢ A ⇒ B ~ R ⇒ S
  same-∀   : (zero ∷ shiftNames η) ⊢ A ~ R → η ⊢ `∀ A ~ `∀ R

infix 4 _⊢ᶜ_~_
_⊢ᶜ_~_ : Ctxᵗ → Ty → Ty → Set
Γ ⊢ᶜ A ~ R = names Γ ⊢ A ~ R

-- Two ordinary types at the same representation depth denote the same
-- representation-universe type. `lock` and `unlock` may give that type
-- different ordinary de Bruijn spellings.
infix 4 _⊢_≈_⊣_
_⊢_≈_⊣_ : Ctxᵗ → Ty → Ty → Ctxᵗ → Set
Γ ⊢ A ≈ B ⊣ Γ′ = ∃[ R ] ((Γ ⊢ᶜ A ~ R) × (Γ′ ⊢ᶜ B ~ R))

shiftRep : ℕ → Ty → Ty
shiftRep zero    R = R
shiftRep (suc n) R = ⇑ᵗ (shiftRep n R)

-- A boundary scope's representation binders occur in its conversion context but
-- not in its exterior context. Thus an exterior representation reading must
-- cross that bind prefix before it can be compared with a conversion type.
SameTyExt : ℕ → Ctxᵗ → Ty → Ctxᵗ → Ty → Set
SameTyExt n Γ A Γ′ B =
  ∃[ R ] ((Γ ⊢ᶜ A ~ R) × (Γ′ ⊢ᶜ B ~ shiftRep n R))

-- The conversion lookup square. Ordinary X names α; α is represented by R;
-- and ordinary A is R read through the current ordinary-name assignment.
infix 4 _∋_:=_
_∋_:=_ : Ctxᵗ → ℕ → Ty → Set
Γ ∋ X := A =
  ∃[ α ] ∃[ R ]
    ((Γ ∋ᵗ X := α) × (Γ ∋rep α := R) × (Γ ⊢ᶜ A ~ R))

------------------------------------------------------------------------
-- 6. Context well-formedness
------------------------------------------------------------------------

infix 4 _∌ʳ_
data _∌ʳ_ : TyCtx → RVar → Set where
  fresh[] : [] ∌ʳ α
  fresh∷  : α ≢ β → Δ ∌ʳ α → (β ∷ Δ) ∌ʳ α

data Unique : TyCtx → Set where
  unique[] : Unique []
  unique∷  : Δ ∌ʳ α → Unique Δ → Unique (α ∷ Δ)

ValidNames : RepCtx → TyCtx → Set
ValidNames Ξ Δ = ∀ {X α} → Δ ∋ˡ X := α → ∃[ b ] Ξ ∋ˡ α := b

record WfCtx (Γ : Ctxᵗ) : Set where
  constructor wf-ctx
  field
    wf-reps  : WfRepCtx (reps Γ)
    wf-names : ValidNames (reps Γ) (names Γ)
    name-fn  : Unique (names Γ)
open WfCtx public

------------------------------------------------------------------------
-- 7. Small formation checks
------------------------------------------------------------------------

empty : Ctxᵗ
empty = [] ∣ []

------------------------------------------------------------------------
-- 8. Renaming the representation universe — the NAME MAP half
------------------------------------------------------------------------

-- A REPRESENTATION-ONLY renaming moves representation variables and
-- leaves every ordinary POSITION exactly where it was.  On a name map
-- that is `map ρ`: a lookup keeps its ordinary index and changes only the
-- representation variable it names.  This section is everything that
-- transport needs from the name map alone; the representation-CONTEXT
-- half — where a payload must move too — is §11 below.

-- `extN n ρ` renames underneath n binders.  It is used at two depths:
-- `n` local `∀`s inside a representation payload, and the `n` parallel
-- representation binders a boundary scope's bind block introduces.
extN : ℕ → Renameᵗ → Renameᵗ
extN zero    ρ = ρ
extN (suc n) ρ = extᵗ (extN n ρ)

-- An INJECTIVE renaming is what a name map needs: `lock` records that the
-- name it deleted is now fresh, and freshness is not preserved by a map
-- that identifies two representation variables.
Injᵗ : Renameᵗ → Set
Injᵗ ρ = ∀ {α β} → ρ α ≡ ρ β → α ≡ β

------------------------------------------------------------------------
-- 9. Representation-variable binders
------------------------------------------------------------------------

shiftBy : ℕ → Ty → Ty
shiftBy zero    R = R
shiftBy (suc n) R = ⇑ᵗ (shiftBy n R)

-- The bind block is parallel: every payload is written over the exterior
-- representation context. Earlier entries are shifted past their list tail.
pushRepBinds : List Ty → RepCtx → RepCtx
pushRepBinds []       Ξ = Ξ
pushRepBinds (R ∷ Rs) Ξ =
  bindR (shiftBy (length Rs) R) ∷ pushRepBinds Rs Ξ

shiftRVars : ℕ → TyCtx → TyCtx
shiftRVars n = map (n +_)

extendReps : List Ty → Ctxᵗ → Ctxᵗ
extendReps Rs (Ξ ∣ Δ) =
  pushRepBinds Rs Ξ ∣ shiftRVars (length Rs) Δ

-- Every bind payload is checked over the SAME exterior representation
-- context. This is the boundary scope's parallel-bind discipline.
-- THE STORE (experiment 2, 2026-09-22; notes/RepStoreSketch.md).  A
-- boundary no longer carries a bind block: the representation a
-- ∀-elimination mints is pushed onto the AMBIENT representation context
-- at index 0, and every existing representation variable — in the
-- context's name map and in every sibling term — moves up by one.
allocate : Ty → Ctxᵗ → Ctxᵗ
allocate R (Ξ ∣ Δ) = (bindR R ∷ Ξ) ∣ shiftNames Δ

-- What one reduction step did to the store: nothing, or one cell.
data Alloc : Set where
  none : Alloc
  new  : Ty → Alloc

apply : Alloc → Ctxᵗ → Ctxᵗ
apply none    Γ = Γ
apply (new R) Γ = allocate R Γ

infix 4 _⊢ᴮ_
data _⊢ᴮ_ (Ξ : RepCtx) : List Ty → Set where
  binds[] : Ξ ⊢ᴮ []
  binds∷  : Ξ ⊢ᴿ R → Ξ ⊢ᴮ Rs → Ξ ⊢ᴮ R ∷ Rs

-- The same fact for an ABSTRACT binding as well: only the payload of a
-- represented one actually moves, but a rep-only weakening has to carry
-- both, so state the shift on bindings rather than on payloads.
shiftByᵇ : ℕ → RepBinding → RepBinding
shiftByᵇ zero    b = b
shiftByᵇ (suc n) b = renRepBinding suc (shiftByᵇ n b)

------------------------------------------------------------------------
-- 10. Inserting and deleting an ordinary name
------------------------------------------------------------------------

infix 4 _⊢+_at_⇒_
data _⊢+_at_⇒_ (α : RVar) : TyCtx → ℕ → TyCtx → Set where
  ins-here  : α ⊢+ Δ at zero ⇒ α ∷ Δ
  ins-there : α ⊢+ Δ at X ⇒ Δ′
    → α ⊢+ β ∷ Δ at suc X ⇒ β ∷ Δ′

infix 4 _⊢-_at_⇒_
data _⊢-_at_⇒_ (α : RVar) : TyCtx → ℕ → TyCtx → Set where
  del-here  : α ⊢- α ∷ Δ at zero ⇒ Δ
  del-there : α ⊢- Δ at X ⇒ Δ′
    → α ⊢- β ∷ Δ at suc X ⇒ β ∷ Δ′

------------------------------------------------------------------------
-- 11. Renaming the representation universe — the CONTEXT half
------------------------------------------------------------------------

-- A REPRESENTATION-ONLY renaming ρ acts on a context by renaming the
-- representation context and renaming the name map POINTWISE (`map ρ`).
-- Ordinary positions never move, so the ordinary spelling of every type,
-- conversion and change is untouched — which is the whole point of
-- `renᴹᴿ`.  `RepWk ρ Ξ Ξ′` is what such a move must supply, and it is
-- exactly what the two induced readings, the conversion typing and the
-- typing judgement all consume.  Three fields are the three `WfCtx`
-- obligations one universe down; the fourth, injectivity, is what a
-- `lock`'s freshness record needs.
--
-- The base instances insert either one abstract binder (`repwk-abst₀`,
-- strong-rep-store.proof.Ctx, for `crossΛᴹ`) or a bind block (`repwk-wkN`,
-- strong-rep-store.proof.RepWeaken, for `Peel`).  `repwk-push` and `repwk-abst`
-- close either instance under the two ways the typing induction goes deeper.

record RepWk (ρ : Renameᵗ) (Ξ Ξ′ : RepCtx) : Set where
  constructor repwk
  field
    wk-inj  : Injᵗ ρ
    wk-look : ∀ {α b} → Ξ ∋ˡ α := b → ∃[ b′ ] (Ξ′ ∋ˡ ρ α := b′)
    wk-bind : ∀ {α b} → Ξ ∋ʳ α := b → Ξ′ ∋ʳ ρ α := renRepBinding ρ b
    wk-reps : WfRepCtx Ξ → WfRepCtx Ξ′
open RepWk public
