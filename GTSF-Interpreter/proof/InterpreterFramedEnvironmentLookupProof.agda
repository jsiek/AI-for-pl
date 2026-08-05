module proof.InterpreterFramedEnvironmentLookupProof where

-- File Charter:
--   * Implements exact environment lookup by structural context recursion.
--   * Returns the stored framed value without reindexing or erasure.
--   * Contains no interpreter call, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; Σ-syntax)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
open import Types

framed-environment-lookup :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ γᵀ γ γ′ x A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : RelatedWorlds.WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  γᵀ ∋ x ⦂ NTI.ctx-imp A A′ p →
  Σ[ V ∈ Value ]
  Σ[ V′ ∈ Value ]
    lookup γ x ≡ just V ×
    lookup γ′ x ≡ just V′ ×
    FramedValueNarrowing
      {A = A} {A′ = A′} {p = p} runtime V V′
framed-environment-lookup
    (value ∷⊑∷ᶠ environment) Z =
  _ , _ , refl , refl , value
framed-environment-lookup
    (value ∷⊑∷ᶠ environment) (S x∈) =
  framed-environment-lookup environment x∈
