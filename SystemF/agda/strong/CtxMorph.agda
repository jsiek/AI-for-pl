module strong.CtxMorph where

-- Strong System F v7 — representation bindings and scope changes.
--
-- A STORE introduces anchors, CONCEALED: a source name stands for one only
-- once a reveal says so.  A SCOPE CHANGE then flips visibility bits, in
-- place.  Because it adds and removes no entry, `dual` is an exact
-- inverse (strong.proof.ScopeDual), which is what `Wrap` needs to send its
-- argument back out.

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
entry abstBind    = anch concealed abstA
entry (repBind R) = anch concealed (bindA R)

applyStore : Store → Ctxᵗ → Ctxᵗ
applyStore []      Δ = Δ
applyStore (b ∷ Θ) Δ = applyStore Θ (entry b ∷ Δ)

infix 4 _⊢ˢ_⇒_
data _⊢ˢ_⇒_ : Ctxᵗ → Store → Ctxᵗ → Set where
  store[]   : ∀ {Δ} → Δ ⊢ˢ [] ⇒ Δ
  store-abst : ∀ {Δ Θ Δ′}
    → (anch concealed abstA ∷ Δ) ⊢ˢ Θ ⇒ Δ′
    → Δ ⊢ˢ abstBind ∷ Θ ⇒ Δ′
  store-bind : ∀ {Δ Θ Δ′ R}
    → Δ ⊢ᴿ R → (anch concealed (bindA R) ∷ Δ) ⊢ˢ Θ ⇒ Δ′
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

-- A change flips ONE bit, and may pass only through entries that are
-- ALREADY CONCEALED.  That second clause is the notes' "rightmost visible
-- source name" condition, stated structurally: a reveal therefore makes
-- its anchor the NEWEST type variable and a conceal removes the newest,
-- exactly as `(+X:=α)(Γ) = Γ,X:=α` and `(-X:=α)` do informally.
infix 4 _⊢δ_⇒_
data _⊢δ_⇒_ : Ctxᵗ → Change → Ctxᵗ → Set where
  rev-here : ∀ {Δ b}
    → (anch concealed b ∷ Δ) ⊢δ reveal zero ⇒ (anch revealed b ∷ Δ)
  rev-under : ∀ {Δ Δ′ b α}
    → Δ ⊢δ reveal α ⇒ Δ′
    → (anch concealed b ∷ Δ) ⊢δ reveal (suc α) ⇒ (anch concealed b ∷ Δ′)
  con-here : ∀ {Δ b}
    → (anch revealed b ∷ Δ) ⊢δ conceal zero ⇒ (anch concealed b ∷ Δ)
  con-under : ∀ {Δ Δ′ b α}
    → Δ ⊢δ conceal α ⇒ Δ′
    → (anch concealed b ∷ Δ) ⊢δ conceal (suc α) ⇒ (anch concealed b ∷ Δ′)

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

renBind : Renameᴿ → AnchorBinding → AnchorBinding
renBind ρ abstA     = abstA
renBind ρ (bindA R) = bindA (renameᴿ ρ R)

renStore : Renameᴿ → Store → Store
renStore ρ []               = []
renStore ρ (abstBind ∷ Θ)   = abstBind ∷ renStore (extᴿ ρ) Θ
renStore ρ (repBind R ∷ Θ)  =
  repBind (renameᴿ ρ R) ∷ renStore (extᴿ ρ) Θ

renChange : Renameᴿ → Change → Change
renChange ρ (reveal α)  = reveal (ρ α)
renChange ρ (conceal α) = conceal (ρ α)

renScope : Renameᴿ → Scope → Scope
renScope ρ = map (renChange ρ)

renBoundaryScope : Renameᴿ → Store → Scope → Scope
renBoundaryScope ρ Θ χ = renScope (extendAnchor (length Θ) ρ) χ

private
  -- notes-v7 §14: α:=ℕ named X, then β abstract named Y.  Concealing Y is
  -- immediate; concealing X passes THROUGH the (now concealed) β.
  nested : Ctxᵗ
  nested = anch revealed abstA ∷ anch revealed (bindA `ℕᴿ) ∷ []

  after-Y : Ctxᵗ
  after-Y = anch concealed abstA ∷ anch revealed (bindA `ℕᴿ) ∷ []

  conceal-Y : nested ⊢δ conceal 0 ⇒ after-Y
  conceal-Y = con-here

  conceal-X : after-Y ⊢δ conceal 1
            ⇒ (anch concealed abstA ∷ anch concealed (bindA `ℕᴿ) ∷ [])
  conceal-X = con-under con-here
