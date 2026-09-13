module strong.notes.probes.V7MergedEntryProbe where

-- PROBE (2026-09-13): the MERGED-ENTRY context.
--
-- A context entry is an ANCHOR that is either concealed or revealed.  The
-- two universes stay separate and get CLEANER coordinates: an anchor's
-- index is its position, full stop; a type variable's index is its
-- position AMONG THE REVEALED.  An anchor is never removed; a type
-- variable enters at `+X:=α` and leaves at `-X:=α`, exactly as now.
--
-- The point: `reveal` and `conceal` FLIP A BIT, so they are
-- LENGTH-PRESERVING.  Anchor indices are therefore stable, `anchorLevel`
-- is unnecessary, and `dual` is an exact inverse — which is what
-- notes/probes/V7DualScopeProbe.agda showed the current design lacks.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map; reverse; length)
open import Data.List.Properties using (unfold-reverse; map-++)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; subst)

open import strong.RepresentationTypes using (Anchor; RepTy; `ℕᴿ; ⇑ᴿ)

------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------

data AnchorBinding : Set where
  abstA : AnchorBinding
  bindA : RepTy → AnchorBinding

data Vis : Set where
  concealed revealed : Vis

-- ONE entry: an anchor, carrying its binding, and whether a source name
-- currently stands for it.
data Ent : Set where
  anch : Vis → AnchorBinding → Ent

Ctxᵗ : Set
Ctxᵗ = List Ent

private
  variable
    Δ Δ′ Δ₁ Δ₂ Δ₃ : Ctxᵗ
    b : AnchorBinding
    v : Vis
    e : Ent
    R : RepTy
    X : ℕ
    α : Anchor

-- Anchors: every entry is one, so the index IS the position.
anchorCount : Ctxᵗ → ℕ
anchorCount = length

infix 4 _∋a_
data _∋a_ : Ctxᵗ → Anchor → Set where
  a-here  : (e ∷ Δ) ∋a zero
  a-there : Δ ∋a α → (e ∷ Δ) ∋a suc α

-- Type variables: the index counts the REVEALED entries.
infix 4 _∋tv_
data _∋tv_ : Ctxᵗ → ℕ → Set where
  tv-here : (anch revealed b ∷ Δ) ∋tv zero
  tv-revealed  : Δ ∋tv X → (anch revealed b ∷ Δ) ∋tv suc X
  tv-concealed : Δ ∋tv X → (anch concealed b ∷ Δ) ∋tv X

-- The two coordinates of one entry.  Note BOTH steps raise the anchor and
-- only the revealed step raises the type variable: that is the whole
-- difference in scope between the two universes.
infix 4 _∋n_:=_
data _∋n_:=_ : Ctxᵗ → ℕ → Anchor → Set where
  n-here : (anch revealed b ∷ Δ) ∋n zero := zero
  n-revealed  : Δ ∋n X := α → (anch revealed b ∷ Δ) ∋n suc X := suc α
  n-concealed : Δ ∋n X := α → (anch concealed b ∷ Δ) ∋n X := suc α

infix 4 _∋r_:=_
data _∋r_:=_ : Ctxᵗ → Anchor → RepTy → Set where
  r-here  : (anch v (bindA R) ∷ Δ) ∋r zero := ⇑ᴿ R
  r-there : Δ ∋r α := R → (e ∷ Δ) ∋r suc α := ⇑ᴿ R

-- The colour: exactly the revealed entries.
scopeᵗ : Ctxᵗ → List ℕ
scopeᵗ [] = []
scopeᵗ (anch revealed b ∷ Δ) = zero ∷ map suc (scopeᵗ Δ)
scopeᵗ (anch concealed b ∷ Δ) = scopeᵗ Δ

------------------------------------------------------------------------
-- Scope changes: flip one bit
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

-- A change may only pass through entries that are ALREADY CONCEALED.
-- That is the notes' "rightmost visible source name" condition, stated
-- structurally instead of as the side judgment `Γ ▷ X:=α`.
infix 4 _⊢δ_⇒_
data _⊢δ_⇒_ : Ctxᵗ → Change → Ctxᵗ → Set where
  rev-here : (anch concealed b ∷ Δ) ⊢δ reveal zero ⇒ (anch revealed b ∷ Δ)
  rev-under : Δ ⊢δ reveal α ⇒ Δ′
    → (anch concealed b ∷ Δ) ⊢δ reveal (suc α) ⇒ (anch concealed b ∷ Δ′)
  con-here : (anch revealed b ∷ Δ) ⊢δ conceal zero ⇒ (anch concealed b ∷ Δ)
  con-under : Δ ⊢δ conceal α ⇒ Δ′
    → (anch concealed b ∷ Δ) ⊢δ conceal (suc α) ⇒ (anch concealed b ∷ Δ′)

infix 4 _⊢χ_⇒_
data _⊢χ_⇒_ : Ctxᵗ → Scope → Ctxᵗ → Set where
  scope[] : Δ ⊢χ [] ⇒ Δ
  scope∷  : ∀ {δ χ} → Δ₁ ⊢δ δ ⇒ Δ₂ → Δ₂ ⊢χ χ ⇒ Δ₃ → Δ₁ ⊢χ δ ∷ χ ⇒ Δ₃

scope-++ : ∀ {χ₁ χ₂} → Δ₁ ⊢χ χ₁ ⇒ Δ₂ → Δ₂ ⊢χ χ₂ ⇒ Δ₃
  → Δ₁ ⊢χ χ₁ ++ χ₂ ⇒ Δ₃
scope-++ scope[] t = t
scope-++ (scope∷ d s) t = scope∷ d (scope-++ s t)

------------------------------------------------------------------------
-- THE RESULT: the dual is an exact inverse
------------------------------------------------------------------------

δ-invert : ∀ {δ} → Δ ⊢δ δ ⇒ Δ′ → Δ′ ⊢δ dualChange δ ⇒ Δ
δ-invert rev-here = con-here
δ-invert (rev-under d) = con-under (δ-invert d)
δ-invert con-here = rev-here
δ-invert (con-under d) = rev-under (δ-invert d)

dual-∷ : ∀ δ χ → dual (δ ∷ χ) ≡ dual χ ++ (dualChange δ ∷ [])
dual-∷ δ χ =
  trans (cong (map dualChange) (unfold-reverse δ χ))
        (map-++ dualChange (reverse χ) (δ ∷ []))

-- Not "up to reordering": the SAME context, on the nose.
χ-invert : ∀ {χ} → Δ ⊢χ χ ⇒ Δ′ → Δ′ ⊢χ dual χ ⇒ Δ
χ-invert scope[] = scope[]
χ-invert {Δ = Δ} {Δ′ = Δ′} (scope∷ {δ = δ} {χ = χ} d s) =
  subst (λ ξ → Δ′ ⊢χ ξ ⇒ Δ) (sym (dual-∷ δ χ))
    (scope-++ (χ-invert s) (scope∷ (δ-invert d) scope[]))

------------------------------------------------------------------------
-- The two universes keep their roles
------------------------------------------------------------------------

-- Anchors are untouched: a change preserves the count …
δ-count : ∀ {δ} → Δ ⊢δ δ ⇒ Δ′ → anchorCount Δ ≡ anchorCount Δ′
δ-count rev-here = refl
δ-count (rev-under d) = cong suc (δ-count d)
δ-count con-here = refl
δ-count (con-under d) = cong suc (δ-count d)

-- … and every anchor stays in scope across it, at the same index.
δ-anchor : ∀ {δ} → Δ ⊢δ δ ⇒ Δ′ → Δ ∋a α → Δ′ ∋a α
δ-anchor rev-here a-here = a-here
δ-anchor rev-here (a-there a) = a-there a
δ-anchor (rev-under d) a-here = a-here
δ-anchor (rev-under d) (a-there a) = a-there (δ-anchor d a)
δ-anchor con-here a-here = a-here
δ-anchor con-here (a-there a) = a-there a
δ-anchor (con-under d) a-here = a-here
δ-anchor (con-under d) (a-there a) = a-there (δ-anchor d a)

-- Type variables are NOT untouched: a reveal makes its anchor the NEWEST
-- type variable (index zero), exactly as `(+X:=α)(Γ) = Γ,X:=α` does now.
reveal-newest : ∀ {Δ Δ′ α} → Δ ⊢δ reveal α ⇒ Δ′ → Δ′ ∋n zero := α
reveal-newest rev-here = n-here
reveal-newest (rev-under d) = n-concealed (reveal-newest d)

-- Dually, a conceal removes the newest — which is the notes' condition
-- that `-X:=α` may only remove the RIGHTMOST visible source name.  Here it
-- is forced by the rule shape: `con-under` passes only concealed entries.
conceal-newest : ∀ {Δ Δ′ α} → Δ ⊢δ conceal α ⇒ Δ′ → Δ ∋n zero := α
conceal-newest con-here = n-here
conceal-newest (con-under d) = n-concealed (conceal-newest d)

-- Hence the OUT-OF-ORDER state is unrepresentable: one cannot reveal an
-- anchor while a newer one is already revealed, so the type-variable order
-- is always the anchor order restricted to the revealed entries.  That was
-- the one claim the merged design rested on.

------------------------------------------------------------------------
-- notes-v7 §14, end to end
------------------------------------------------------------------------

--   α:=ℕ , X:=α , β , Y:=β     (β abstract and named Y; α holds ℕ, named X)
§14 : Ctxᵗ
§14 = anch revealed abstA ∷ anch revealed (bindA `ℕᴿ) ∷ []

--   χ = (-Y:=β) ; (-X:=α)      -- Y is anchor 0, X is anchor 1
χ§14 : Scope
χ§14 = conceal 0 ∷ conceal 1 ∷ []

§14ᵢ : Ctxᵗ
§14ᵢ = anch concealed abstA ∷ anch concealed (bindA `ℕᴿ) ∷ []

enter : §14 ⊢χ χ§14 ⇒ §14ᵢ
enter = scope∷ con-here (scope∷ (con-under con-here) scope[])

-- `-X` passed THROUGH the (now concealed) β, and the dual puts X back
-- where it was rather than on top.
dual-χ§14 : dual χ§14 ≡ reveal 1 ∷ reveal 0 ∷ []
dual-χ§14 = refl

leave : §14ᵢ ⊢χ dual χ§14 ⇒ §14
leave = χ-invert enter

-- The round trip is an equality, not an equivalence.
round-trip : §14ᵢ ⊢χ dual χ§14 ⇒ §14
round-trip = scope∷ (rev-under rev-here) (scope∷ rev-here scope[])

-- Colours agree throughout, and the interior's is empty.
colour-outside : scopeᵗ §14 ≡ 0 ∷ 1 ∷ []
colour-outside = refl

colour-inside : scopeᵗ §14ᵢ ≡ []
colour-inside = refl
