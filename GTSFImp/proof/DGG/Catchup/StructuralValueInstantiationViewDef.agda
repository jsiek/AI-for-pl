module
  proof.DGG.Catchup.StructuralValueInstantiationViewDef where

-- File Charter:
--   * Classifies value source shapes that can face a target type app.
--   * Excludes lambdas, constants, and matched target-wrapper shapes.

open import Types using (TyCtx)
import Consistency
import Conversion
open import CastTerms using
  (Term; Value; Inert; RevealValue; ConcealValue;
   Λ_; _⟨_⟩; _↑_; _↓_)


data ValueTypeAppSourceView {Δ : TyCtx} : Term Δ → Set where
  type-app-source-Λ : ∀ {V}
    → Value V
    → ValueTypeAppSourceView (Λ V)

  type-app-source-cast : ∀ {V μ A B} {c : μ Consistency.⊢ A ∼ B}
    → Value V
    → Inert c
    → ValueTypeAppSourceView (V ⟨ c ⟩)

  type-app-source-reveal : ∀ {V A B} {c : Conversion.Conv↑ Δ A B}
    → Value V
    → RevealValue c
    → ValueTypeAppSourceView (V ↑ c)

  type-app-source-conceal : ∀ {V A B} {c : Conversion.Conv↓ Δ A B}
    → Value V
    → ConcealValue c
    → ValueTypeAppSourceView (V ↓ c)
