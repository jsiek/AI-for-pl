module strong.CtxMorph where

-- Strong System F -- experimental two-universe context morphisms.
--
-- A morphism remains a pair. Its `binds` are a parallel block of fresh
-- representation-variable binders. Its `changes` sequentially bind and
-- anti-bind ordinary type variables. Every change carries both the ordinary
-- de Bruijn position and the representation variable named at that position.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; reverse; length)
open import Data.Product using (_,_; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import strong.Types using (Ty; `ℕ; ⇑ᵗ)
open import strong.Ctx

private
  variable
    Γ Γᵢ Γᶜ : Ctxᵗ
    Ξ : RepCtx
    Δ Δ′ Δ₁ Δ₂ Δ₃ : TyCtx
    Rs : List Ty
    R : Ty
    b : RepBinding
    X : ℕ
    α β : RVar

------------------------------------------------------------------------
-- 1. Representation-variable binders
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
-- context. This is the morphism's parallel-bind discipline.
infix 4 _⊢ᴮ_
data _⊢ᴮ_ (Ξ : RepCtx) : List Ty → Set where
  binds[] : Ξ ⊢ᴮ []
  binds∷  : Ξ ⊢ᴿ R → Ξ ⊢ᴮ Rs → Ξ ⊢ᴮ R ∷ Rs

------------------------------------------------------------------------
-- 2. Ordinary-variable binders and anti-binders
------------------------------------------------------------------------

data Change : Set where
  lock   : ℕ → RVar → Change
  unlock : ℕ → RVar → Change

private
  variable
    δ : Change
    χ : List Change

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

insert-functional : α ⊢+ Δ at X ⇒ Δ₁
  → α ⊢+ Δ at X ⇒ Δ₂
  → Δ₁ ≡ Δ₂
insert-functional ins-here ins-here = refl
insert-functional (ins-there i) (ins-there i′) =
  cong (_ ∷_) (insert-functional i i′)

delete-functional : α ⊢- Δ at X ⇒ Δ₁
  → α ⊢- Δ at X ⇒ Δ₂
  → Δ₁ ≡ Δ₂
delete-functional del-here del-here = refl
delete-functional (del-there d) (del-there d′) =
  cong (_ ∷_) (delete-functional d d′)

-- `lock` records freshness of the result and `unlock` demands freshness of
-- its input. Thus one representation variable never has two simultaneous
-- ordinary names, and the two changes are exact inverses. The Ξ index makes
-- the carried representation-variable occurrence well scoped.
ValidRVar : RepCtx → RVar → Set
ValidRVar Ξ α = ∃[ b ] Ξ ∋ˡ α := b

infix 4 _∣_⊢δ_⇒_
data _∣_⊢δ_⇒_ (Ξ : RepCtx) : TyCtx → Change → TyCtx → Set where
  step-lock : ValidRVar Ξ α → α ⊢- Δ at X ⇒ Δ′ → Fresh α Δ′
    → Ξ ∣ Δ ⊢δ lock X α ⇒ Δ′
  step-unlock : ValidRVar Ξ α → Fresh α Δ → α ⊢+ Δ at X ⇒ Δ′
    → Ξ ∣ Δ ⊢δ unlock X α ⇒ Δ′

insert-delete : α ⊢- Δ at X ⇒ Δ′ → α ⊢+ Δ′ at X ⇒ Δ
insert-delete del-here = ins-here
insert-delete (del-there d) = ins-there (insert-delete d)

delete-insert : α ⊢+ Δ at X ⇒ Δ′ → α ⊢- Δ′ at X ⇒ Δ
delete-insert ins-here = del-here
delete-insert (ins-there i) = del-there (delete-insert i)

dualChange : Change → Change
dualChange (lock X α)   = unlock X α
dualChange (unlock X α) = lock X α

dual-step : Ξ ∣ Δ ⊢δ δ ⇒ Δ′
  → Ξ ∣ Δ′ ⊢δ dualChange δ ⇒ Δ
dual-step (step-lock valid d fresh) =
  step-unlock valid fresh (insert-delete d)
dual-step (step-unlock valid fresh i) =
  step-lock valid (delete-insert i) fresh

-- Changes retain the current design's head-LAST order: the tail acts first.
infix 4 _∣_⊢χ_⇒_
data _∣_⊢χ_⇒_ (Ξ : RepCtx)
  : TyCtx → List Change → TyCtx → Set where
  changes[] : Ξ ∣ Δ ⊢χ [] ⇒ Δ
  changes∷  : Ξ ∣ Δ₁ ⊢χ χ ⇒ Δ₂
    → Ξ ∣ Δ₂ ⊢δ δ ⇒ Δ₃
    → Ξ ∣ Δ₁ ⊢χ δ ∷ χ ⇒ Δ₃

change-functional : Ξ ∣ Δ ⊢δ δ ⇒ Δ₁
  → Ξ ∣ Δ ⊢δ δ ⇒ Δ₂
  → Δ₁ ≡ Δ₂
change-functional (step-lock valid d fresh)
                  (step-lock valid′ d′ fresh′) =
  delete-functional d d′
change-functional (step-unlock valid fresh i)
                  (step-unlock valid′ fresh′ i′) =
  insert-functional i i′

changes-functional : Ξ ∣ Δ ⊢χ χ ⇒ Δ₁
  → Ξ ∣ Δ ⊢χ χ ⇒ Δ₂
  → Δ₁ ≡ Δ₂
changes-functional changes[] changes[] = refl
changes-functional (changes∷ cs st) (changes∷ cs′ st′)
  with changes-functional cs cs′
changes-functional (changes∷ cs st) (changes∷ cs′ st′) | refl =
  change-functional st st′

dual : List Change → List Change
dual χ = map dualChange (reverse χ)

-- Move a change underneath `n` representation binders. Ordinary positions
-- do not move; only the carried representation-variable occurrence does.
underRepBinds : ℕ → Change → Change
underRepBinds n (lock X α)   = lock X (n + α)
underRepBinds n (unlock X α) = unlock X (n + α)

------------------------------------------------------------------------
-- 3. Context morphisms and their two induced contexts
------------------------------------------------------------------------

record CtxMorph : Set where
  constructor morph
  field
    binds   : List Ty
    changes : List Change
open CtxMorph public

numBinds : CtxMorph → ℕ
numBinds Θ = length (binds Θ)

-- A crossing argument is already inside the representation bind block of
-- the boundary it crosses. Its dual therefore binds no new representation
-- variables and simply reverses the ordinary-variable changes.
dualMorph : CtxMorph → CtxMorph
dualMorph Θ = morph [] (dual (changes Θ))

-- Rewind retains the bind block and performs the inverse changes before the
-- original changes. This is the syntax used by CancelR and IdPush.
rewind : CtxMorph → CtxMorph
rewind Θ = morph (binds Θ) (dual (changes Θ) ++ changes Θ)

-- Move the outer morphism's ordinary-variable effects into the inner one.
-- The outer binders already occur in the exterior of the resulting inner
-- boundary; the inner bind block shifts their representation occurrences.
infixl 5 _⋉_
_⋉_ : CtxMorph → CtxMorph → CtxMorph
Θ₁ ⋉ Θ₂ =
  morph (binds Θ₁)
        (changes Θ₁ ++ map (underRepBinds (numBinds Θ₁)) (changes Θ₂))

-- When a boundary crosses a fresh `Λ` binder, ordinary position zero names
-- the representation variable immediately outside its own bind prefix.
addLock0 : CtxMorph → CtxMorph
addLock0 Θ =
  morph (binds Θ) (changes Θ ++ (lock 0 (numBinds Θ) ∷ []))

-- Instantiation prepends a represented binder and gives it ordinary name 0.
-- The unlock acts first (head-LAST order); every pre-existing change then
-- moves past both the new ordinary name and the new representation binder.
instantiate : Ty → CtxMorph → CtxMorph
instantiate R Θ =
  morph (R ∷ binds Θ)
        (map shiftChange (changes Θ) ++ (unlock 0 0 ∷ []))
  where
  shiftChange : Change → Change
  shiftChange (lock X α)   = lock (suc X) (suc α)
  shiftChange (unlock X α) = unlock (suc X) (suc α)

-- The interior performs every change.
infix 4 _⊢ⁱ_⇒_
data _⊢ⁱ_⇒_ (Γ : Ctxᵗ) (Θ : CtxMorph) : Ctxᵗ → Set where
  interior : ∀ {Δ′}
    → reps (extendReps (binds Θ) Γ)
      ∣ names (extendReps (binds Θ) Γ) ⊢χ changes Θ ⇒ Δ′
    → Γ ⊢ⁱ Θ ⇒ (reps (extendReps (binds Θ) Γ) ∣ Δ′)

-- The conversion context performs `unlock`s but skips `lock`s, so both the
-- concealed variable and its representation are available to the conversion.
-- It is therefore the UNION of the names live anywhere along the morphism,
-- not the name map at any one point of the run.
--
-- THE RE-UNLOCK CLAUSE (2026-09-17).  Reading it as a union forces a third
-- clause.  Skipping a `lock X α` leaves α live, so a LATER `unlock` of that
-- same α — the shape every `dualMorph`/`rewind` composite has, since a dual
-- inverts each lock with an unlock — meets a name that is already there and
-- the freshness premise of `conv-unlock` fails.  Without this clause
-- `rewind Θ` and `Θ′ ⋉ Θ` have NO conversion context whenever Θ locks, so
-- CancelR's and IdPush's contracta are untypeable: that is the wall the
-- fourth reduction example walked into (notes/RepresentationReductionExamples
-- §4, `no-rewind-conv` / `no-cancel-inner-conv`).
--
-- The clause does not widen the judgement where the old one applied: the two
-- unlock clauses are mutually exclusive (`fresh-not-lookup`), so the
-- conversion context stays a FUNCTION of the change list, which is what
-- determinism for CancelR/IdPush/TyPeelR-⟪⟫ consumes
-- (`conv-changes-functional`, `conversion-functional`).
--
-- WHY THE POSITION IS DROPPED.  `conv-lock` already ignores its position:
-- skipping the lock keeps α exactly where it was.  The paired unlock must
-- therefore keep it there too — re-inserting it at the interior position X
-- would move a name the conversion context never moved.  The positions of a
-- conversion context are the interior's positions with the locked names left
-- in place, and this clause is what makes that reading hold through a dual.
infix 4 _∣_⊢χᶜ_⇒_
data _∣_⊢χᶜ_⇒_ (Ξ : RepCtx)
  : TyCtx → List Change → TyCtx → Set where
  conv[] : Ξ ∣ Δ ⊢χᶜ [] ⇒ Δ
  conv-lock : ValidRVar Ξ α → Ξ ∣ Δ₁ ⊢χᶜ χ ⇒ Δ₂
    → Ξ ∣ Δ₁ ⊢χᶜ lock X α ∷ χ ⇒ Δ₂
  conv-unlock : ValidRVar Ξ α
    → Ξ ∣ Δ₁ ⊢χᶜ χ ⇒ Δ₂
    → Fresh α Δ₂
    → α ⊢+ Δ₂ at X ⇒ Δ₃
    → Ξ ∣ Δ₁ ⊢χᶜ unlock X α ∷ χ ⇒ Δ₃
  conv-unlock-live : ∀ {Y} → ValidRVar Ξ α
    → Ξ ∣ Δ₁ ⊢χᶜ χ ⇒ Δ₂
    → Δ₂ ∋ˡ Y := α
    → Ξ ∣ Δ₁ ⊢χᶜ unlock X α ∷ χ ⇒ Δ₂

conv-changes-functional : Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ₁
  → Ξ ∣ Δ ⊢χᶜ χ ⇒ Δ₂
  → Δ₁ ≡ Δ₂
conv-changes-functional conv[] conv[] = refl
conv-changes-functional (conv-lock valid cs) (conv-lock valid′ cs′) =
  conv-changes-functional cs cs′
conv-changes-functional (conv-unlock valid cs fresh i)
                        (conv-unlock valid′ cs′ fresh′ i′)
  with conv-changes-functional cs cs′
conv-changes-functional (conv-unlock valid cs fresh i)
                        (conv-unlock valid′ cs′ fresh′ i′) | refl =
  insert-functional i i′
conv-changes-functional (conv-unlock-live valid cs d)
                        (conv-unlock-live valid′ cs′ d′) =
  conv-changes-functional cs cs′
-- the mixed pairs are impossible: one says α is FRESH in the tail's
-- output, the other says α is LOOKED UP there.
conv-changes-functional (conv-unlock valid cs fresh i)
                        (conv-unlock-live valid′ cs′ d′)
  with conv-changes-functional cs cs′
... | refl = ⊥-elim (fresh-not-lookup fresh d′)
conv-changes-functional (conv-unlock-live valid cs d)
                        (conv-unlock valid′ cs′ fresh′ i′)
  with conv-changes-functional cs cs′
... | refl = ⊥-elim (fresh-not-lookup fresh′ d)

infix 4 _⊢ᶜ_⇒_
data _⊢ᶜ_⇒_ (Γ : Ctxᵗ) (Θ : CtxMorph) : Ctxᵗ → Set where
  conversion : ∀ {Δ′}
    → reps (extendReps (binds Θ) Γ)
      ∣ names (extendReps (binds Θ) Γ) ⊢χᶜ changes Θ ⇒ Δ′
    → Γ ⊢ᶜ Θ ⇒ (reps (extendReps (binds Θ) Γ) ∣ Δ′)

interior-functional : ∀ {Θ : CtxMorph}
  → Γ ⊢ⁱ Θ ⇒ Γᵢ → Γ ⊢ⁱ Θ ⇒ Γᶜ → Γᵢ ≡ Γᶜ
interior-functional (interior cs) (interior cs′) =
  cong (_ ∣_) (changes-functional cs cs′)

conversion-functional : ∀ {Θ : CtxMorph}
  → Γ ⊢ᶜ Θ ⇒ Γᵢ → Γ ⊢ᶜ Θ ⇒ Γᶜ → Γᵢ ≡ Γᶜ
conversion-functional (conversion cs) (conversion cs′) =
  cong (_ ∣_) (conv-changes-functional cs cs′)

-- A complete morphism witness names both induced contexts. The output
-- well-formedness fields are currently explicit obligations; they will become
-- derived lemmas once context transport is developed.
record MorphWf (Γ : Ctxᵗ) (Θ : CtxMorph)
               (Γᵢ Γᶜ : Ctxᵗ) : Set where
  constructor mw
  field
    mw-exterior  : WfCtx Γ
    mw-binds     : reps Γ ⊢ᴮ binds Θ
    mw-interior  : Γ ⊢ⁱ Θ ⇒ Γᵢ
    mw-conversion : Γ ⊢ᶜ Θ ⇒ Γᶜ
    mw-interior-wf : WfCtx Γᵢ
    mw-conversion-wf : WfCtx Γᶜ
open MorphWf public

------------------------------------------------------------------------
-- 4. Concrete boundary shapes
------------------------------------------------------------------------

TyBetaMorph : CtxMorph
TyBetaMorph = morph (`ℕ ∷ []) (unlock 0 0 ∷ [])

TyBetaCtx : Ctxᵗ
TyBetaCtx = (bindR `ℕ ∷ []) ∣ (zero ∷ [])

TyBeta-interior : empty ⊢ⁱ TyBetaMorph ⇒ TyBetaCtx
TyBeta-interior =
  interior
    (changes∷ changes[] (step-unlock (_ , here) fresh[] ins-here))

TyBeta-conversion : empty ⊢ᶜ TyBetaMorph ⇒ TyBetaCtx
TyBeta-conversion =
  conversion
    (conv-unlock (_ , here) conv[] fresh[] ins-here)

TyBetaCtx-wf : WfCtx TyBetaCtx
TyBetaCtx-wf =
  wf-ctx (wf-bindR wfᴿ-ℕ wf-reps[])
         (λ { here → _ , here })
         (unique∷ fresh[] unique[])

TyBeta-mw : MorphWf empty TyBetaMorph TyBetaCtx TyBetaCtx
TyBeta-mw =
  mw wf-empty (binds∷ wfᴿ-ℕ binds[])
     TyBeta-interior TyBeta-conversion TyBetaCtx-wf TyBetaCtx-wf

-- Crossing an argument under `ΛX` removes only ordinary X. Its abstract
-- representation variable remains, and the dual restores X exactly.
ΛXCtx : Ctxᵗ
ΛXCtx = underΛ empty

crossΛ : reps ΛXCtx ∣ names ΛXCtx ⊢δ lock 0 0 ⇒ []
crossΛ = step-lock (_ , here) del-here fresh[]

uncrossΛ : reps ΛXCtx ∣ [] ⊢δ unlock 0 0 ⇒ names ΛXCtx
uncrossΛ = dual-step crossΛ
