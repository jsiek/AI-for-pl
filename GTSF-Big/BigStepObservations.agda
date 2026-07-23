module BigStepObservations where

-- File Charter:
--   * Runtime observations induced by the structural big-step semantics.
--   * Separates value convergence, blame, total convergence, divergence, and
--     the divergence-or-blame observation used by the DGG.
--   * Depends only on `BigStep` and the Nu term/result syntax.

open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_)

open import BigStep
open import NuReduction using (StoreChanges)
open import NuTerms using (Term; Value; blame)

ValueConvergesᵇ : Term → Set
ValueConvergesᵇ M =
  ∃[ V ] (Σ[ χs ∈ StoreChanges ] ((M ⇓[ χs ] V) × Value V))

Blamesᵇ : Term → Set
Blamesᵇ M = Σ[ χs ∈ StoreChanges ] (M ⇓[ χs ] blame)

Convergesᵇ : Term → Set
Convergesᵇ M = ∃[ R ] (Σ[ χs ∈ StoreChanges ] (M ⇓[ χs ] R))

Divergesᵇ : Term → Set
Divergesᵇ M = ¬ Convergesᵇ M

-- On closed well-typed runtime terms, progress and adequacy make
-- `¬ ValueConvergesᵇ M` mean exactly that `M` diverges or evaluates to blame.
-- The negative form avoids a classical choice between the two alternatives.
DivergesOrBlamesᵇ : Term → Set
DivergesOrBlamesᵇ M = ¬ ValueConvergesᵇ M

value-convergence-is-convergence :
  ∀ {M} →
  ValueConvergesᵇ M →
  Convergesᵇ M
value-convergence-is-convergence (V , χs , M⇓V , vV) =
  V , χs , M⇓V

blame-is-convergence :
  ∀ {M} →
  Blamesᵇ M →
  Convergesᵇ M
blame-is-convergence (χs , M⇓blame) =
  blame , χs , M⇓blame
