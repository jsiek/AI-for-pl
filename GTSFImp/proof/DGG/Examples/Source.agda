module proof.DGG.Examples.Source where

-- File Charter:
--   * Provides source-term constructors shared by the DGG example suite.
--   * Exports `cast`, the annotated-identity idiom that asks the ordinary
--     compiler to insert a consistency cast at an application boundary.
--   * Contains source syntax only; it does not expose cast-calculus terms.

open import Types using (Ty)
open import GradualTerms

cast : ∀ {Δ} → Label → Ty Δ → GTerm Δ → GTerm Δ
cast ℓ A M = (ƛ A ⇒ ` 0) ·[ ℓ ] M
