module strong.Weakening where

-- Weakening and well-formedness lemmas for the type context.  Free type variables
-- (_∈ᵗ_), renaming preserves well-formedness (wf-rename-fv, wf-⇑-*), and — the
-- payoff of the shift-free representation lookup — a looked-up representation is
-- well-formed in its PREFIX (∋:=-⊢).

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (Σ; _×_; _,_; ∃)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import strong.Types
open import strong.Context

private
  variable
    Δ′ : TCtx
    ρ : Renameᵗ

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

-- weaken a well-formed type through one entry
wf-⇑-abst : Δ ⊢ A → (abst ∷ Δ) ⊢ ⇑ᵗ A
wf-⇑-abst wfA = wf-rename-fv {ρ = suc} (λ y → skip-abst (fv-scope wfA y)) wfA

wf-⇑-rvld : Δ ⊢ A → (rvld C ∷ Δ) ⊢ ⇑ᵗ A
wf-⇑-rvld wfA = wf-rename-fv {ρ = suc} (λ y → skip-rvld (fv-scope wfA y)) wfA

wf-⇑-xrvld : Δ ⊢ A → (xrvld C ∷ Δ) ⊢ ⇑ᵗ A
wf-⇑-xrvld wfA =
  wf-rename-fv {ρ = suc} (λ y → skip-xrvld (fv-scope wfA y)) wfA

------------------------------------------------------------------------
-- A looked-up representation is well formed in its prefix
------------------------------------------------------------------------

-- With shift-free representation lookup, the rep stored at X is a type over X's
-- tail — which is exactly the prefix Δ ↓ X — and a well-formed context makes each
-- such rep well-formed in its own tail.  So ∋:=-⊢ is a direct projection of ⊢ Δ,
-- with no weakening, no shifting, and no side conditions.
∋:=-⊢ : ⊢ Δ → Δ ∋ X := A → (Δ ↓ X) ⊢ A
∋:=-⊢ (⊢rvld ⊢Δ Δ⊢A) here           = Δ⊢A
∋:=-⊢ (⊢abst ⊢Δ)     (skip-abst p)  = ∋:=-⊢ ⊢Δ p
∋:=-⊢ (⊢rvld ⊢Δ _)   (skip-rvld p)  = ∋:=-⊢ ⊢Δ p
∋:=-⊢ (⊢xrvld ⊢Δ)    (skip-xrvld p) = ∋:=-⊢ ⊢Δ p
