module proof.EndpointMLB.Core.EndpointLowerBoundDef where

-- File Charter:
--   * Defines a common lower bound of two endpoints under well-formed
--     indexed type imprecision.
--   * Contains no selector, maximality algorithm, coherence theorem, or
--     operational DGG result.

open import Data.Product using (_×_)

open import Imprecision using (idᵢ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Types using (Ty; TyCtx)


CommonLowerBoundᵢ : TyCtx → Ty → Ty → Ty → Set
CommonLowerBoundᵢ Δ A B C =
  idᵢ Δ ∣ Δ ⊢ C ⊑ A ⊣ Δ ×
  idᵢ Δ ∣ Δ ⊢ C ⊑ B ⊣ Δ
