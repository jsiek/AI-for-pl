module strong.Weakening where

-- Weakening and well-formedness lemmas for the type context.  Free type
-- variables (_∈ᵗ_), renaming preserves well-formedness (wf-rename-fv, wf-⇑-*),
-- a representation's variables are deeper than its index (∋:=-hi), weakening
-- through a marker (wk-cncl), and — the payoff of the tightened `cncl` marker —
-- representation lookup yields a well-formed type (∋:=-⊢).

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (<-trans; suc-injective)
open import Data.Product using (Σ; _×_; _,_; ∃)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; subst)
open import strong.Types
open import strong.TypeSubst using (rename-cong)
open import strong.Context

private
  variable
    Δ′ : TCtx
    ρ : Renameᵗ
    W : ℕ

------------------------------------------------------------------------
-- Free type variables of a type
------------------------------------------------------------------------

infix 4 _∈ᵗ_
data _∈ᵗ_ : ℕ → Ty → Set where
  fv-var : ∀ {Y}     → Y ∈ᵗ (` Y)
  fv-⇒l  : ∀ {Y A B} → Y ∈ᵗ A → Y ∈ᵗ (A ⇒ B)
  fv-⇒r  : ∀ {Y A B} → Y ∈ᵗ B → Y ∈ᵗ (A ⇒ B)
  fv-∀   : ∀ {Y A}   → suc Y ∈ᵗ A → Y ∈ᵗ (`∀ A)

-- free variables of a well-formed type are in scope
fv-scope : Δ ⊢ A → Y ∈ᵗ A → Δ ∋tv Y
fv-scope (wf-var p) fv-var    = p
fv-scope wf-ℕ ()
fv-scope wf-𝔹 ()
fv-scope (wf-⇒ a b) (fv-⇒l y) = fv-scope a y
fv-scope (wf-⇒ a b) (fv-⇒r y) = fv-scope b y
fv-scope (wf-∀ a) (fv-∀ y)    with fv-scope a y
... | skip-abst p             = p

-- free variables commute with renaming
fv-rename : (ρ : Renameᵗ) (A : Ty) {Y : ℕ}
          → Y ∈ᵗ renameᵗ ρ A → ∃ λ Y′ → (Y ≡ ρ Y′) × (Y′ ∈ᵗ A)
fv-rename ρ (` Z) fv-var      = Z , refl , fv-var
fv-rename ρ `ℕ ()
fv-rename ρ `𝔹 ()
fv-rename ρ (A ⇒ B) (fv-⇒l y) with fv-rename ρ A y
... | Y′ , eq , y′            = Y′ , eq , fv-⇒l y′
fv-rename ρ (A ⇒ B) (fv-⇒r y) with fv-rename ρ B y
... | Y′ , eq , y′            = Y′ , eq , fv-⇒r y′
fv-rename ρ (`∀ A) (fv-∀ y)   with fv-rename (extᵗ ρ) A y
... | zero , () , _
... | suc Y′ , eq , y′        = Y′ , suc-injective eq , fv-∀ y′

------------------------------------------------------------------------
-- Renaming preserves well-formedness (restricted to the free variables)
------------------------------------------------------------------------

wf-rename-fv : ∀ {ρ} → (∀ {Y} → Y ∈ᵗ A → Δ′ ∋tv ρ Y) → Δ ⊢ A → Δ′ ⊢ renameᵗ ρ A
wf-rename-fv h (wf-var p) = wf-var (h fv-var)
wf-rename-fv h wf-ℕ       = wf-ℕ
wf-rename-fv h wf-𝔹       = wf-𝔹
wf-rename-fv h (wf-⇒ a b) =
  wf-⇒ (wf-rename-fv (λ y → h (fv-⇒l y)) a) (wf-rename-fv (λ y → h (fv-⇒r y)) b)
wf-rename-fv {Δ′ = Δ′} {ρ = ρ} h (wf-∀ {A = A₀} a) = wf-∀ (wf-rename-fv h′ a)
  where h′ : ∀ {Y} → Y ∈ᵗ A₀ → (abst ∷ Δ′) ∋tv extᵗ ρ Y
        h′ {zero}  _ = here-abst
        h′ {suc Y} y = skip-abst (h (fv-∀ y))

-- weaken a well-formed type through one counting entry
wf-⇑-abst : Δ ⊢ A → (abst ∷ Δ) ⊢ ⇑ᵗ A
wf-⇑-abst wfA = wf-rename-fv {ρ = suc} (λ y → skip-abst (fv-scope wfA y)) wfA

wf-⇑-rvld : Δ ⊢ A → (rvld C ∷ Δ) ⊢ ⇑ᵗ A
wf-⇑-rvld wfA = wf-rename-fv {ρ = suc} (λ y → skip-rvld (fv-scope wfA y)) wfA

------------------------------------------------------------------------
-- The representation looked up at X mentions only variables deeper than X
------------------------------------------------------------------------

∋:=-hi : Δ ∋ X := A → Y ∈ᵗ A → X < Y
∋:=-hi (here {A = A₀}) y       with fv-rename suc A₀ y
... | Y′ , refl , _            = s≤s z≤n
∋:=-hi (skip-abst {A = A₀} p) y with fv-rename suc A₀ y
... | Y′ , refl , y′           = s≤s (∋:=-hi p y′)
∋:=-hi (skip-rvld {A = A₀} p) y with fv-rename suc A₀ y
... | Y′ , refl , y′           = s≤s (∋:=-hi p y′)
∋:=-hi (skip-cncl _ p) y       = ∋:=-hi p y

------------------------------------------------------------------------
-- Weaken a well-formed type through a marker it does not mention
------------------------------------------------------------------------

ext-id : (i : ℕ) → extᵗ (λ z → z) i ≡ i
ext-id zero    = refl
ext-id (suc i) = refl

rename-id : (A : Ty) → renameᵗ (λ z → z) A ≡ A
rename-id (` X)   = refl
rename-id `ℕ      = refl
rename-id `𝔹      = refl
rename-id (A ⇒ B) = cong₂ _⇒_ (rename-id A) (rename-id B)
rename-id (`∀ A)  = cong `∀ (trans (rename-cong ext-id A) (rename-id A))

wk-cncl : Δ ⊢ A → (∀ {Y} → Y ∈ᵗ A → W < Y) → (cncl W ∷ Δ) ⊢ A
wk-cncl {Δ = Δ} {A = A} {W = W} wfA h =
  subst (λ z → (cncl W ∷ Δ) ⊢ z) (rename-id A)
        (wf-rename-fv {ρ = λ z → z} (λ y → skip-cncl (h y) (fv-scope wfA y)) wfA)

------------------------------------------------------------------------
-- A looked-up representation is well formed
------------------------------------------------------------------------

-- With the tightened marker (skip-cncl needs n < X), representation lookup now
-- yields a well-formed type directly, given a well-formed context.  Any marker
-- skipped en route to X conceals a variable shallower than X (n < X), while the
-- representation's free variables are all deeper than X (∋:=-hi); so no marker
-- can block them.  This SUBSUMES the earlier `ConcealCtx` predicate: the
-- (conceal) rule no longer needs to carry it.
∋:=-⊢ : ⊢ Δ → Δ ∋ X := A → Δ ⊢ A
∋:=-⊢ (⊢rvld ⊢Δ Δ⊢A₀) here             = wf-⇑-rvld Δ⊢A₀
∋:=-⊢ (⊢abst ⊢Δ)      (skip-abst p)    = wf-⇑-abst (∋:=-⊢ ⊢Δ p)
∋:=-⊢ (⊢rvld ⊢Δ _)    (skip-rvld p)    = wf-⇑-rvld (∋:=-⊢ ⊢Δ p)
∋:=-⊢ (⊢cncl ⊢Δ _)    (skip-cncl n<X p) =
  wk-cncl (∋:=-⊢ ⊢Δ p) (λ y → <-trans n<X (∋:=-hi p y))
