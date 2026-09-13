module strong.CtxMorph where

-- Strong System F v7 — representation bindings and scope changes.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_; _++_; map; reverse; length)

open import strong.RepresentationTypes
open import strong.Ctx

------------------------------------------------------------------------
-- Representation bindings Θ
------------------------------------------------------------------------

data RepBind : Set where
  abstBind : RepBind
  repBind  : RepTy → RepBind

Store : Set
Store = List RepBind

entry : RepBind → Ent
entry abstBind    = abst
entry (repBind R) = bind R

applyStore : Store → Ctxᵗ → Ctxᵗ
applyStore []       Δ = Δ
applyStore (b ∷ Θ) Δ = applyStore Θ (entry b ∷ Δ)

infix 4 _⊢ˢ_⇒_
data _⊢ˢ_⇒_ : Ctxᵗ → Store → Ctxᵗ → Set where
  store[]   : ∀ {Δ} → Δ ⊢ˢ [] ⇒ Δ
  store-abst : ∀ {Δ Θ Δ′}
    → (abst ∷ Δ) ⊢ˢ Θ ⇒ Δ′
    → Δ ⊢ˢ abstBind ∷ Θ ⇒ Δ′
  store-bind : ∀ {Δ Θ Δ′ R}
    → Δ ⊢ᴿ R → (bind R ∷ Δ) ⊢ˢ Θ ⇒ Δ′
    → Δ ⊢ˢ repBind R ∷ Θ ⇒ Δ′

------------------------------------------------------------------------
-- Scope changes χ
------------------------------------------------------------------------

data Change : Set where
  reveal  : Anchor → Change
  conceal : Anchor → Change

Scope : Set
Scope = List Change

dualChange : Change → Change
dualChange (reveal α)  = conceal α
dualChange (conceal α) = reveal α

dual : Scope → Scope
dual χ = map dualChange (reverse χ)

-- Exact pop.  Anchors may intervene; another source name may not.
infix 4 _▷_↘_
data _▷_↘_ : Ctxᵗ → Anchor → Ctxᵗ → Set where
  pop-here  : ∀ {Δ α} → (name α ∷ Δ) ▷ α ↘ Δ
  pop-abst  : ∀ {Δ Δ′ α} → Δ ▷ α ↘ Δ′
            → (abst ∷ Δ) ▷ suc α ↘ (abst ∷ Δ′)
  pop-bind  : ∀ {Δ Δ′ α R} → Δ ▷ α ↘ Δ′
            → (bind R ∷ Δ) ▷ suc α ↘ (bind R ∷ Δ′)

infix 4 _⊢δ_⇒_
data _⊢δ_⇒_ : Ctxᵗ → Change → Ctxᵗ → Set where
  step-reveal : ∀ {Δ α}
    → Δ ∋a α → Unoccupied Δ α
    → Δ ⊢δ reveal α ⇒ name α ∷ Δ
  step-conceal : ∀ {Δ Δ′ α}
    → Δ ▷ α ↘ Δ′
    → Δ ⊢δ conceal α ⇒ Δ′

infix 4 _⊢χ_⇒_
data _⊢χ_⇒_ : Ctxᵗ → Scope → Ctxᵗ → Set where
  scope[] : ∀ {Δ} → Δ ⊢χ [] ⇒ Δ
  scope∷  : ∀ {Δ₁ Δ₂ Δ₃ δ χ}
    → Δ₁ ⊢δ δ ⇒ Δ₂ → Δ₂ ⊢χ χ ⇒ Δ₃
    → Δ₁ ⊢χ δ ∷ χ ⇒ Δ₃

------------------------------------------------------------------------
-- Reindexing when representation bindings move
------------------------------------------------------------------------

shiftAnchor : ℕ → Anchor → Anchor
shiftAnchor n α = n + α

shiftChange : ℕ → Change → Change
shiftChange n (reveal α)  = reveal (shiftAnchor n α)
shiftChange n (conceal α) = conceal (shiftAnchor n α)

shiftScope : ℕ → Scope → Scope
shiftScope n = map (shiftChange n)

extendAnchor : ℕ → Renameᴿ → Renameᴿ
extendAnchor zero    ρ = ρ
extendAnchor (suc n) ρ = extᴿ (extendAnchor n ρ)

renStore : Renameᴿ → Store → Store
renStore ρ []                   = []
renStore ρ (abstBind ∷ Θ) = abstBind ∷ renStore (extᴿ ρ) Θ
renStore ρ (repBind R ∷ Θ) =
  repBind (renameᴿ ρ R) ∷ renStore (extᴿ ρ) Θ

renChange : Renameᴿ → Change → Change
renChange ρ (reveal α)  = reveal (ρ α)
renChange ρ (conceal α) = conceal (ρ α)

renScope : Renameᴿ → Scope → Scope
renScope ρ = map (renChange ρ)

renBoundaryScope : Renameᴿ → Store → Scope → Scope
renBoundaryScope ρ Θ χ = renScope (extendAnchor (length Θ) ρ) χ

private
  nested : Ctxᵗ
  nested = name 0 ∷ bind `ℕᴿ ∷ name 0 ∷ bind `ℕᴿ ∷ []

  after-Y : Ctxᵗ
  after-Y = bind `ℕᴿ ∷ name 0 ∷ bind `ℕᴿ ∷ []

  pop-Y : nested ▷ 0 ↘ after-Y
  pop-Y = pop-here

  pop-X : after-Y ▷ 1 ↘ bind `ℕᴿ ∷ bind `ℕᴿ ∷ []
  pop-X = pop-bind pop-here
