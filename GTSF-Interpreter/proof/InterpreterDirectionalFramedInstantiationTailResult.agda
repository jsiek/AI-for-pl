module proof.InterpreterDirectionalFramedInstantiationTailResult where

-- File Charter:
--   * Removes the static allocation frame from returned instantiation-tail
--     values while retaining the exact future runtime relation.
--   * Composes the pre-allocation and post-allocation world extensions once.
--   * Contains no interpreter call, recursion, reduction, or catch-up result.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)

open import ImprecisionWf using
  (_ˣ⊑★; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Framed.InterpreterFramedTypeTransport using
  ( left-operational-value-unlift
  ; left-typed-value-unlift
  ; paired-operational-value-unlift
  ; paired-typed-value-unlift
  )
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterFramedValueNarrowingProperties using
  (framed-value-operational; framed-value-typed)
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties using
  (runtime-narrowing-weaken)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.MaximalLowerBoundsWf using
  (⊑-lift∀ᵢ; ⊑-source-liftνᵢ)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-tail-result :
  ∀ {W W′ U U′ Z Z′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
    {θ θ′ α α′ A A′ V V′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {T : WorldRelation Z Z′} →
  AssumptionMembershipUnique Φ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  WorldExtension R S →
  WorldExtension S T →
  FramedValueResult
    ρ′ (seal-name α ∷ θ) (seal-name α′ ∷ θ′)
    (⊑-lift∀ᵢ p) T V V′ →
  FramedValueResult ρ θ θ′ p T V V′
paired-tail-result
    {θ = θ} {θ′ = θ′} {α = α} {α′ = α′}
    {A = A} {A′ = A′} {p = p}
    unique runtime R≤S S≤T
    (framed-result runtime↑ value) =
  framed-result runtimeT
    (paired-unlifted-value {p = p} unique
      (paired-typed-value-unlift
        {θ = θ} {θ′ = θ′} {α = α} {α′ = α′}
        {A = A} {A′ = A′}
        (framed-value-typed value))
      (paired-operational-value-unlift
        {θ = θ} {θ′ = θ′} {α = α} {α′ = α′}
        {A = A} {A′ = A′}
        (framed-value-operational value))
      value)
  where
  R≤T =
    PersistentWorldProperties.world-extension-trans R≤S S≤T

  runtimeT =
    runtime-narrowing-weaken R≤T
      (left-world-typed runtime↑)
      (right-world-typed runtime↑)
      runtime

left-tail-result :
  ∀ {W W′ U U′ Z Z′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ}
    {θ θ′ α A A′ V V′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {T : WorldRelation Z Z′} →
  AssumptionMembershipUnique Φ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  WorldExtension R S →
  WorldExtension S T →
  FramedValueResult
    ρ′ (seal-name α ∷ θ) θ′
    (⊑-source-liftνᵢ p) T V V′ →
  FramedValueResult ρ θ θ′ p T V V′
left-tail-result
    {θ = θ} {θ′ = θ′} {α = α}
    {A = A} {A′ = A′} {p = p}
    unique runtime R≤S S≤T
    (framed-result runtime↑ value) =
  framed-result runtimeT
    (left-unlifted-value {p = p} unique
      (left-typed-value-unlift
        {θ = θ} {θ′ = θ′} {α = α}
        {A = A} {A′ = A′}
        (framed-value-typed value))
      (left-operational-value-unlift
        {θ = θ} {θ′ = θ′} {α = α}
        {A = A} {A′ = A′}
        (framed-value-operational value))
      value)
  where
  R≤T =
    PersistentWorldProperties.world-extension-trans R≤S S≤T

  runtimeT =
    runtime-narrowing-weaken R≤T
      (left-world-typed runtime↑)
      (right-world-typed runtime↑)
      runtime
