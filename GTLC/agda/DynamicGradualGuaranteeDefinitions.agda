module DynamicGradualGuaranteeDefinitions where

-- File Charter:
--   * Public runtime-observation predicates used to state the GTLC dynamic
--     gradual guarantee.
--   * Defines termination, divergence, blame, and diverge-or-blame
--     observations for source terms via compilation.
--   * Depends only on public language, cast-calculus, and compilation modules.

open import Agda.Builtin.List using ([])
open import Data.Product using (Σ-syntax; ∃-syntax; _×_)
open import Data.Sum using (_⊎_)

open import GTLC
open import CastCalculus
open import Compile using (compile)

_⇓_ : Term → Termᶜ → Set
M ⇓ V =
  ∃[ A ] (Σ[ wt ∈ ([] ⊢ M ⦂ A) ] (compile wt —↠ᶜ V × Result V))

Diverges : Term → Set
Diverges M = ∃[ A ] (Σ[ wt ∈ ([] ⊢ M ⦂ A) ] (Divergesᶜ (compile wt)))

Blames : Term → Set
Blames M = ∃[ ℓ ] (M ⇓ blame {ℓ = ℓ})

DivergeOrBlameᶜ : Termᶜ → Set
DivergeOrBlameᶜ M′ =
  ∀ N′
  → M′ —↠ᶜ N′
  → Blameᶜ N′ ⊎ ∃[ N″ ] N′ —→ᶜ N″

DivergeOrBlame : Term → Set
DivergeOrBlame M =
  ∃[ A ] (Σ[ wt ∈ ([] ⊢ M ⦂ A) ] (DivergeOrBlameᶜ (compile wt)))
