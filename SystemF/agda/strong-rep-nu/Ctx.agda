module strong-rep-nu.Ctx where

-- File Charter:
--   * THE TWO DE BRUIJN UNIVERSES AND EVERY RELATION OVER THEM.
--     §1 `RVar`/`RepBinding`/`RepCtx`/`TyCtx`/`Ctxᵗ = reps ∣ names`;
--     §2 the lookup family; §3 ordinary type formation `_⊢ᵗ_` with
--     `underΛ`; §4 representation payloads; §5 the two readings of a
--     `Ty` (`_⊢_~_`, `_⊢_≈_⊣_`) and the lookup square `_∋_:=_`;
--     §6 `WfCtx`; §§8–11 `extN`/`Injᵗ`, `shiftBy`, THE STORE
--     (`allocate`/`Alloc`/`apply`), insert/delete, and `RepWk`.
--   * DEFINITIONS ONLY: every lemma lives in proof/Ctx.agda.
--   * THE INVARIANT.  `names Γ` holds EXACTLY the ordinary type
--     variables in scope, each entry the representation variable it
--     names; a representation-only renaming leaves every ordinary
--     POSITION where it was, acting on the name map by `map ρ`.
-- Commentary: Commentary.md § Ctx.agda

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (_×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import strong-rep-nu.Types
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

-- one context's ordinary names read through a representation renaming,
-- against a second context's store
-- Commentary.md § Ctx.agda / renNameCtx
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

shiftReps : TyCtx → TyCtx
shiftReps = map suc

-- A term-level `Λ` and the premise of ordinary `∀` formation bind both an
-- ordinary type variable and an abstract representation variable.
underΛ : Ctxᵗ → Ctxᵗ
underΛ (Ξ ∣ Δ) = (abstR ∷ Ξ) ∣ (zero ∷ shiftReps Δ)

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
  same-∀   : (zero ∷ shiftReps η) ⊢ A ~ R → η ⊢ `∀ A ~ `∀ R

infix 4 _⊢ᶜ_~_
_⊢ᶜ_~_ : Ctxᵗ → Ty → Ty → Set
Γ ⊢ᶜ A ~ R = names Γ ⊢ A ~ R

-- Two ordinary types at the same representation depth denote the same
-- representation-universe type. `unbind` and `bind` may give that type
-- different ordinary de Bruijn spellings.
infix 4 _⊢_≈_⊣_
_⊢_≈_⊣_ : Ctxᵗ → Ty → Ty → Ctxᵗ → Set
Γ ⊢ A ≈ B ⊣ Γ′ = ∃[ R ] ((Γ ⊢ᶜ A ~ R) × (Γ′ ⊢ᶜ B ~ R))

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

-- §8 is what transport needs from the NAME MAP alone; §11 is the
-- representation-context half.
-- Commentary.md § Ctx.agda / extN, Injᵗ

-- `extN n ρ` renames underneath n binders: the n local `∀`s inside a
-- representation payload.
extN : ℕ → Renameᵗ → Renameᵗ
extN zero    ρ = ρ
extN (suc n) ρ = extᵗ (extN n ρ)

-- injectivity is what an `unbind`'s freshness record needs
Injᵗ : Renameᵗ → Set
Injᵗ ρ = ∀ {α β} → ρ α ≡ ρ β → α ≡ β

------------------------------------------------------------------------
-- 9. Representation-variable binders
------------------------------------------------------------------------

shiftBy : ℕ → Ty → Ty
shiftBy zero    R = R
shiftBy (suc n) R = ⇑ᵗ (shiftBy n R)
-- THE STORE (experiment 2, 2026-09-22; notes/RepStoreSketch.md): a
-- ∀-elimination's representation is pushed onto the AMBIENT
-- representation context at index 0, and everything else moves up one.
-- Commentary.md § Ctx.agda / THE STORE
allocate : Ty → Ctxᵗ → Ctxᵗ
allocate R (Ξ ∣ Δ) = (bindR R ∷ Ξ) ∣ shiftReps Δ

-- What one reduction step did to the store: nothing, or one cell.
data Alloc : Set where
  none : Alloc
  new  : Ty → Alloc

apply : Alloc → Ctxᵗ → Ctxᵗ
apply none    Γ = Γ
apply (new R) Γ = allocate R Γ

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

-- `RepWk ρ Ξ Ξ′` is what a representation-only move must supply:
-- three fields for `WfCtx`'s three obligations one universe down,
-- plus injectivity.  Instances: `repwk-abst₀`, `repwk-cons₀`,
-- `repwk-abst` (proof/Ctx.agda).
-- Commentary.md § Ctx.agda / RepWk

record RepWk (ρ : Renameᵗ) (Ξ Ξ′ : RepCtx) : Set where
  constructor repwk
  field
    wk-inj  : Injᵗ ρ
    wk-look : ∀ {α b} → Ξ ∋ˡ α := b → ∃[ b′ ] (Ξ′ ∋ˡ ρ α := b′)
    wk-bind : ∀ {α b} → Ξ ∋ʳ α := b → Ξ′ ∋ʳ ρ α := renRepBinding ρ b
    wk-reps : WfRepCtx Ξ → WfRepCtx Ξ′
open RepWk public
