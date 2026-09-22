module strong-rep-store.notes.RepresentationVariablesProbe where

-- Strong System F -- probe for separate type-variable and representation-
-- variable de Bruijn universes.
--
-- This file isolates the proposed context design from the live development.
-- It reuses strong-rep-store.Types unchanged.  A free variable of a term type is
-- an
-- ordinary type variable; a free variable of a representation payload is a
-- representation variable.  A `∀` inside either type binds an ordinary local
-- type variable in the usual way.  The relation `_⊢_~_` records the change of
-- free-variable universe explicitly.

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.List using (List; []; _∷_; map; reverse; length)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import strong-rep-store.Types
  using (Ty; `_; `ℕ; `𝔹; _⇒_; `∀; ⇑ᵗ)

------------------------------------------------------------------------
-- 1. The two contexts
------------------------------------------------------------------------

RVar : Set
RVar = ℕ

-- The payload of `bindR R` is a `Ty` over representation variables,
-- not a `Ty` over the ordinary type-variable context.
data RepBinding : Set where
  abstR : RepBinding
  bindR : Ty → RepBinding

RepCtx : Set
RepCtx = List RepBinding

-- Each ordinary type variable in scope points to the representation variable
-- that it names.  Hidden ordinary variables have no entry here.
TyCtx : Set
TyCtx = List RVar

record Ctxᵗ : Set where
  constructor _∣_
  field
    reps  : RepCtx
    names : TyCtx
open Ctxᵗ public

infix 4 _∋_:=_
data _∋_:=_ {A : Set} : List A → ℕ → A → Set where
  here  : ∀ {x xs} → (x ∷ xs) ∋ zero := x
  there : ∀ {x y xs i} → xs ∋ i := x → (y ∷ xs) ∋ suc i := x

-- An ordinary type-variable lookup returns its representation variable.
infix 4 _∋ᵗ_:=_
_∋ᵗ_:=_ : Ctxᵗ → ℕ → RVar → Set
Γ ∋ᵗ X := α = names Γ ∋ X := α

-- A representation-variable lookup returns its binding.  The probe does not
-- yet transport a represented payload out through the intervening binders;
-- that belongs to the representation-context substitution layer.
infix 4 _∋ʳ_:=_
_∋ʳ_:=_ : Ctxᵗ → RVar → RepBinding → Set
Γ ∋ʳ α := b = reps Γ ∋ α := b

private
  variable
    Γ : Ctxᵗ
    Ξ : RepCtx
    Δ Δ′ Δ₁ Δ₂ Δ₃ : TyCtx
    b : RepBinding
    A B R S : Ty
    X i : ℕ
    α β : RVar

------------------------------------------------------------------------
-- 2. Ordinary types and representation types use the same syntax
------------------------------------------------------------------------

-- A term-level `Λ` extends BOTH global universes.  Existing representation-
-- variable references shift because the new abstract representation variable
-- occupies slot zero.
shiftReps : TyCtx → TyCtx
shiftReps = map suc

underΛ : Ctxᵗ → Ctxᵗ
underΛ (Ξ ∣ Δ) = (abstR ∷ Ξ) ∣ (zero ∷ shiftReps Δ)

-- `η ⊢ A ~ R` says that ordinary type A and representation type R have the
-- same shape, with each free ordinary variable translated through η.  Under
-- `∀`, index zero is the locally bound type variable on both sides; the old
-- free-variable correspondence shifts to indices one and above.  No new
-- representation variable is allocated by this clause.
infix 4 _⊢_~_
data _⊢_~_ (η : TyCtx) : Ty → Ty → Set where
  same-var : η ∋ X := α → η ⊢ ` X ~ ` α
  same-ℕ   : η ⊢ `ℕ ~ `ℕ
  same-𝔹   : η ⊢ `𝔹 ~ `𝔹
  same-⇒   : η ⊢ A ~ R → η ⊢ B ~ S → η ⊢ A ⇒ B ~ R ⇒ S
  same-∀   : (zero ∷ shiftReps η) ⊢ A ~ R → η ⊢ `∀ A ~ `∀ R

infix 4 _⊢ᶜ_~_
_⊢ᶜ_~_ : Ctxᵗ → Ty → Ty → Set
Γ ⊢ᶜ A ~ R = names Γ ⊢ A ~ R

-- Representation payloads have a mixed de Bruijn interpretation.  The first
-- `n` indices are ordinary type variables bound by enclosing payload `∀`s;
-- indices `n + α` are free representation variables from Ξ.
infix 4 _⊢ref[_]_
data _⊢ref[_]_ (Ξ : RepCtx) (n : ℕ) : ℕ → Set where
  local-ref : i < n → Ξ ⊢ref[ n ] i
  free-ref  : Ξ ∋ α := b → Ξ ⊢ref[ n ] (n + α)

infix 4 _⊢ᴿ[_]_
data _⊢ᴿ[_]_ (Ξ : RepCtx) (n : ℕ) : Ty → Set where
  wfᴿ-var : Ξ ⊢ref[ n ] i → Ξ ⊢ᴿ[ n ] ` i
  wfᴿ-ℕ   : Ξ ⊢ᴿ[ n ] `ℕ
  wfᴿ-𝔹   : Ξ ⊢ᴿ[ n ] `𝔹
  wfᴿ-⇒   : Ξ ⊢ᴿ[ n ] R → Ξ ⊢ᴿ[ n ] S → Ξ ⊢ᴿ[ n ] R ⇒ S
  wfᴿ-∀   : Ξ ⊢ᴿ[ suc n ] R → Ξ ⊢ᴿ[ n ] `∀ R

-- Each concrete representation binding is checked outside its own binder.
data WfRepCtx : RepCtx → Set where
  wf-reps[] : WfRepCtx []
  wf-abstR  : WfRepCtx Ξ → WfRepCtx (abstR ∷ Ξ)
  wf-bindR  : Ξ ⊢ᴿ[ zero ] R → WfRepCtx Ξ → WfRepCtx (bindR R ∷ Ξ)

------------------------------------------------------------------------
-- 3. Boundary scope representation binders
------------------------------------------------------------------------

-- A boundary scope's `binds` are PARALLEL representation-variable binders.
-- Their payloads are read outside the whole block, so the earlier list entries
-- are shifted past the entries in their tail, as in the live `pushBinds`.
shiftBy : ℕ → Ty → Ty
shiftBy zero    R = R
shiftBy (suc n) R = ⇑ᵗ (shiftBy n R)

pushRepBinds : List Ty → RepCtx → RepCtx
pushRepBinds []       Ξ = Ξ
pushRepBinds (R ∷ Rs) Ξ =
  bindR (shiftBy (length Rs) R) ∷ pushRepBinds Rs Ξ

shiftRVars : ℕ → TyCtx → TyCtx
shiftRVars n = map (n +_)

extendReps : List Ty → Ctxᵗ → Ctxᵗ
extendReps Rs (Ξ ∣ Δ) =
  pushRepBinds Rs Ξ ∣ shiftRVars (length Rs) Δ

------------------------------------------------------------------------
-- 4. Changes bind and anti-bind ordinary type variables
------------------------------------------------------------------------

data Change : Set where
  lock   : ℕ → RVar → Change
  unlock : ℕ → RVar → Change

private
  variable
    δ : Change
    χ : List Change

-- Inserting/removing at an ordinary de Bruijn position.  The carried
-- representation variable is not inserted into or removed from `RepCtx`.
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

infix 4 _⊢δ_⇒_
data _⊢δ_⇒_ : TyCtx → Change → TyCtx → Set where
  step-lock   : α ⊢- Δ at X ⇒ Δ′ → Δ ⊢δ lock X α ⇒ Δ′
  step-unlock : α ⊢+ Δ at X ⇒ Δ′ → Δ ⊢δ unlock X α ⇒ Δ′

dualChange : Change → Change
dualChange (lock X α)   = unlock X α
dualChange (unlock X α) = lock X α

dual-step : Δ ⊢δ δ ⇒ Δ′ → Δ′ ⊢δ dualChange δ ⇒ Δ
dual-step (step-lock del-here) = step-unlock ins-here
dual-step (step-lock (del-there d)) with dual-step (step-lock d)
dual-step (step-lock (del-there d)) | step-unlock i =
  step-unlock (ins-there i)
dual-step (step-unlock ins-here) = step-lock del-here
dual-step (step-unlock (ins-there i)) with dual-step (step-unlock i)
dual-step (step-unlock (ins-there i)) | step-lock d =
  step-lock (del-there d)

infix 4 _⊢χ_⇒_
data _⊢χ_⇒_ : TyCtx → List Change → TyCtx → Set where
  changes[] : Δ ⊢χ [] ⇒ Δ
  -- As in the live design, the list is applied head-LAST: its tail runs
  -- first, then its head.
  changes∷  : Δ₁ ⊢χ χ ⇒ Δ₂ → Δ₂ ⊢δ δ ⇒ Δ₃
            → Δ₁ ⊢χ δ ∷ χ ⇒ Δ₃

dual : List Change → List Change
dual χ = map dualChange (reverse χ)

------------------------------------------------------------------------
-- 5. Boundary scopes
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    binds   : List Ty
    changes : List Change
open Boundary public

-- The bind block extends only the representation-variable universe.  Its
-- existing ordinary-name references shift by the size of that block.  The
-- changes then insert and remove ordinary names while leaving the resulting
-- representation context fixed.
infix 4 _⊢ᵐ_⇒_
data _⊢ᵐ_⇒_ (Γ : Ctxᵗ) (Θ : Boundary) : Ctxᵗ → Set where
  apply-boundary : ∀ {Δ′}
    → names (extendReps (binds Θ) Γ) ⊢χ changes Θ ⇒ Δ′
    → Γ ⊢ᵐ Θ ⇒ (reps (extendReps (binds Θ) Γ) ∣ Δ′)

------------------------------------------------------------------------
-- 6. Concrete indexing checks
------------------------------------------------------------------------

empty : Ctxᵗ
empty = [] ∣ []

-- `ΛX` binds ordinary X and abstract representation variable α together.
ΛX : Ctxᵗ
ΛX = underΛ empty

_ : reps ΛX ≡ abstR ∷ []
_ = refl

_ : names ΛX ≡ zero ∷ []
_ = refl

-- Crossing under `ΛX` anti-binds X but retains α; the dual binds X back.
cross-X : names ΛX ⊢δ lock 0 0 ⇒ []
cross-X = step-lock del-here

uncross-X : [] ⊢δ unlock 0 0 ⇒ names ΛX
uncross-X = dual-step cross-X

-- Type application first binds α to ℕ, then introduces ordinary X as a
-- name for α.  No ordinary type variable is introduced by `binds` itself.
β-reps : Ctxᵗ
β-reps = extendReps (`ℕ ∷ []) empty

_ : reps β-reps ≡ bindR `ℕ ∷ []
_ = refl

_ : names β-reps ≡ []
_ = refl

β-name : names β-reps ⊢δ unlock 0 0 ⇒ zero ∷ []
β-name = step-unlock ins-here

TyBetaBoundary : Boundary
TyBetaBoundary = boundary (`ℕ ∷ []) (unlock 0 0 ∷ [])

TyBetaCtx : Ctxᵗ
TyBetaCtx = (bindR `ℕ ∷ []) ∣ (zero ∷ [])

TyBetaCtx-ok : empty ⊢ᵐ TyBetaBoundary ⇒ TyBetaCtx
TyBetaCtx-ok = apply-boundary (changes∷ changes[] (step-unlock ins-here))

-- With X older than Y, the name map is [Y↦β, X↦α] = [0,1].  Locking X
-- removes ordinary slot 1.  Y consequently remains as ordinary slot 0;
-- α remains representation slot 1 and can be restored at the same position.
ΛXΛY : Ctxᵗ
ΛXΛY = underΛ (underΛ empty)

_ : names ΛXΛY ≡ zero ∷ suc zero ∷ []
_ = refl

hide-X : names ΛXΛY ⊢δ lock 1 1 ⇒ zero ∷ []
hide-X = step-lock (del-there del-here)

show-X : zero ∷ [] ⊢δ unlock 1 1 ⇒ names ΛXΛY
show-X = dual-step hide-X

-- The same ordinary type has a representation-universe reading obtained
-- solely from the name map.
XY⇒YX : ΛXΛY ⊢ᶜ (` 1 ⇒ ` 0) ~ (` 1 ⇒ ` 0)
XY⇒YX = same-⇒ (same-var (there here)) (same-var here)

-- In the payload `∀ Z. Z ⇒ α`, index zero denotes the locally bound Z and
-- index one denotes the surrounding representation variable α.  The `∀`
-- does not add an entry to `RepCtx`.
∀-payload : zero ∷ [] ⊢ `∀ (` 0 ⇒ ` 1) ~ `∀ (` 0 ⇒ ` 1)
∀-payload = same-∀ (same-⇒ (same-var here) (same-var (there here)))
