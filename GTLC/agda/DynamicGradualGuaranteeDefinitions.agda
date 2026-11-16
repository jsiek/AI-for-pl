module DynamicGradualGuaranteeDefinitions where

-- File Charter:
--   * Public runtime-observation predicates used to state the GTLC dynamic
--     gradual guarantee.
--   * Defines termination, divergence, blame, and diverge-or-blame
--     observations for source terms via compilation.
--   * Defines the observation of a value, used to state the observational form
--     of the guarantee.
--   * Depends only on public language, cast-calculus, and compilation modules.

open import Agda.Builtin.List using ([])
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_)
open import Data.Sum using (_⊎_)

open import GTLC
open import CastCalculus
open import Compile using (compile)

_⇓_ : Term → Termᶜ → Set
M ⇓ V =
  ∃[ A ] (Σ[ wt ∈ ([] ⊢ M ⦂ A) ] (compile wt —↠ V × Result V))

Diverges : Term → Set
Diverges M = ∃[ A ] (Σ[ wt ∈ ([] ⊢ M ⦂ A) ] (Divergesᶜ (compile wt)))

Blames : Term → Set
Blames M = ∃[ ℓ ] (M ⇓ blame {ℓ = ℓ})

DivergeOrBlameᶜ : Termᶜ → Set
DivergeOrBlameᶜ M′ =
  ∀ N′
  → M′ —↠ N′
  → Blameᶜ N′ ⊎ ∃[ N″ ] N′ —→ N″

DivergeOrBlame : Term → Set
DivergeOrBlame M =
  ∃[ A ] (Σ[ wt ∈ ([] ⊢ M ⦂ A) ] (DivergeOrBlameᶜ (compile wt)))

-- What a value shows to an observer: its numeral, or that it is a function.
-- Injections into ★ and function wrappers are not observable.
data Observation : Set where
  nat-obs : Nat → Observation
  fun-obs : Observation

observe : ∀ {V} → Valueᶜ V → Observation
observe (V-$ {n = n}) = nat-obs n
observe V-ƛ = fun-obs
observe (V-cast! vV) = observe vV
observe (V-cast↦ vV) = fun-obs
