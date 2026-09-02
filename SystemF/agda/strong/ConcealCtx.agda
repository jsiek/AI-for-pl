module strong.ConcealCtx where

-- The predicate `ConcealCtx Δ X` describes the possible shapes of the type
-- context at a conceal on the variable at index X.  It is built from one
-- constructor for the context at creation (WrapReveal) and one for each way a
-- conceal's context changes during reduction, and it implies that X's
-- representation is well-formed:   ConcealCtx Δ X → Δ ∋ X := A → Δ ⊢ A.

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (<-trans; <⇒≢; suc-injective)
open import Data.Product using (Σ; _×_; _,_; ∃)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; trans; subst)
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

wk-cncl : Δ ⊢ A → (∀ {Y} → Y ∈ᵗ A → W ≢ Y) → (cncl W ∷ Δ) ⊢ A
wk-cncl {Δ = Δ} {A = A} {W = W} wfA h =
  subst (λ z → (cncl W ∷ Δ) ⊢ z) (rename-id A)
        (wf-rename-fv {ρ = λ z → z} (λ y → skip-cncl (h y) (fv-scope wfA y)) wfA)

------------------------------------------------------------------------
-- Conceal contexts
------------------------------------------------------------------------

data ConcealCtx : TCtx → ℕ → Set where
  new   : Δ ⊢ A          → ConcealCtx (rvld A ∷ Δ) zero    -- birth (WrapReveal)
  ·abst : ConcealCtx Δ X → ConcealCtx (abst   ∷ Δ) (suc X)  -- pushed under a Λ
  ·rvld : ConcealCtx Δ X → ConcealCtx (rvld C ∷ Δ) (suc X)  -- pushed under a reveal
  ·cncl : W < X → ConcealCtx Δ X → ConcealCtx (cncl W ∷ Δ) X -- pushed under an outer conceal

ConcealCtx-⊢ : ConcealCtx Δ X → Δ ∋ X := A → Δ ⊢ A
ConcealCtx-⊢ (new wfA)      here            = wf-⇑-rvld wfA
ConcealCtx-⊢ (·abst cc)     (skip-abst ∋)   = wf-⇑-abst (ConcealCtx-⊢ cc ∋)
ConcealCtx-⊢ (·rvld cc)     (skip-rvld ∋)   = wf-⇑-rvld (ConcealCtx-⊢ cc ∋)
ConcealCtx-⊢ (·cncl W<X cc) (skip-cncl _ ∋) =
  wk-cncl (ConcealCtx-⊢ cc ∋) (λ y → <⇒≢ (<-trans W<X (∋:=-hi ∋ y)))
