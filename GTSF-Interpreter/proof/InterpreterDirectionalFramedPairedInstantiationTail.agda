module proof.InterpreterDirectionalFramedPairedInstantiationTail where

-- File Charter:
--   * Composes paired semantic instantiation with its paired reveal coercion
--     in each directional terminal observation.
--   * Runs at the exact paired allocation relation and then rebases the
--     returned ambient value at the pre-allocation relation.
--   * Contains no recursive definition, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_)

open import ImprecisionWf using
  (_ˣ⊑ˣ_; ⇑ᵢ; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterReachableCoercionNarrowing
open import Core.InterpreterFuel using
  (coerceValue-terminal-stable; instantiateValue-terminal-stable)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (TerminalStable)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  (assumption-membership-unique-matched)
open import proof.InterpreterDirectionalFramedInstantiationTailResult using
  (paired-tail-result)
open import proof.InterpreterDirectionalSequence using
  ( directional-chain-backward
  ; directional-chain-forward
  ; directional-chain-target-blame
  )
open import proof.InterpreterDirectionalTransport using
  ( backward-extension-base
  ; backward-result-map
  ; forward-extension-base
  ; forward-result-map
  )
open import proof.InterpreterInstantiationTail using
  (instantiation-tail)
open import proof.MaximalLowerBoundsWf using
  (⊑-lift∀ᵢ)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-instantiation-tail-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
    {θ θ′ A A′ B B′ C C′ V V′ c c′}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pA⇑ :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {q :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {R : WorldRelation W W′} →
  (unique : AssumptionMembershipUnique Φ) →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (lift :
    NTI.LiftStoreⁱ
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′) →
  (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  (allocated :
    RuntimeNarrowing
      (allocate-both R (type-narrowing pA) θ~θ′)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) pA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ)
      (seal-name (freshSealName W′) ∷ θ′)) →
  (action :
    ReachableComponentCoercionNarrowing
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) pA⇑ ∷ ρ′)
      (apply-coercion c) (apply-coercion c′)
      q (⊑-lift∀ᵢ p)) →
  FramedValueNarrowing
    {A = `∀ C} {A′ = `∀ C′}
    {p = ImprecisionWf.∀ⁱ q}
    runtime V V′ →
  FramedDirectionalPairedInstantiateValueSimulation
    forward-direction index →
  FramedDirectionalCoercionSimulation
    forward-direction index →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ p) R
    (instantiation-tail W θ A c V)
    (instantiation-tail W′ θ′ A′ c′ V′)
    index
paired-instantiation-tail-forward
    {index} {W} {W′} {ρ = ρ} {ρ′ = ρ′}
    {θ = θ} {θ′ = θ′} {A = A} {A′ = A′}
    {V = V} {V′ = V′} {c = c} {c′ = c′}
    {p = p} {pA = pA} {pA⇑ = pA⇑} {q = q}
    {R = R}
    unique runtime lift θ~θ′ allocated action value
    instantiate coercion =
  forward-extension-base
    {left-index = index}
    {value-result = FramedValueResult ρ θ θ′ p}
    {R = R}
    {S = allocate-both R (type-narrowing pA) θ~θ′}
    {left = instantiation-tail W θ A c V}
    {right = instantiation-tail W′ θ′ A′ c′ V′}
    allocation-extension
    (forward-result-map
      {left-index = index}
      {source-result =
        FramedValueResult
          (NTI.store-matched zero (⇑ᵗ A)
            zero (⇑ᵗ A′) pA⇑ ∷ ρ′)
          (seal-name (freshSealName W) ∷ θ)
          (seal-name (freshSealName W′) ∷ θ′)
          (⊑-lift∀ᵢ p)}
      {target-result = FramedValueResult ρ θ θ′ p}
      {R = allocate-both R (type-narrowing pA) θ~θ′}
      {left = instantiation-tail W θ A c V}
      {right = instantiation-tail W′ θ′ A′ c′ V′}
      chained
      (paired-tail-result
        unique runtime allocation-extension))
  where
  allocation-extension =
    extension-both extension-refl

  chained =
    directional-chain-forward
      {W = allocate W A θ}
      {W′ = allocate W′ A′ θ′}
      {left-index = index}
      {head-result =
        FramedValueResult
          (NTI.store-matched zero (⇑ᵗ A)
            zero (⇑ᵗ A′) pA⇑ ∷ ρ′)
          (seal-name (freshSealName W) ∷ θ)
          (seal-name (freshSealName W′) ∷ θ′) q}
      {continuation-result =
        FramedValueResult
          (NTI.store-matched zero (⇑ᵗ A)
            zero (⇑ᵗ A′) pA⇑ ∷ ρ′)
          (seal-name (freshSealName W) ∷ θ)
          (seal-name (freshSealName W′) ∷ θ′)
          (⊑-lift∀ᵢ p)}
      {R = allocate-both R (type-narrowing pA) θ~θ′}
      {left-head =
        instantiateValue
          (allocate W A θ) (freshSealName W) V}
      {right-head =
        instantiateValue
          (allocate W′ A′ θ′) (freshSealName W′) V′}
      {left-continuation =
        λ U Q →
          coerceValue U
            (seal-name (freshSealName W) ∷ θ) c Q}
      {right-continuation =
        λ U′ Q′ →
          coerceValue U′
            (seal-name (freshSealName W′) ∷ θ′) c′ Q′}
      (instantiate unique runtime lift θ~θ′ allocated value)
      (λ
        { R≤S (framed-result runtimeS result) →
            coercion
              (assumption-membership-unique-matched unique)
              runtimeS action result
        })
      refl
      (λ U′ Q′ → refl)
      (λ { {n} {o} terminal eq k →
        instantiateValue-terminal-stable
          {W = allocate W A θ}
          {α = freshSealName W} {V = V}
          {n = n} {o = o} terminal eq k
        })
      (λ { {n} {o} terminal eq k →
        instantiateValue-terminal-stable
          {W = allocate W′ A′ θ′}
          {α = freshSealName W′} {V = V′}
          {n = n} {o = o} terminal eq k
        })
      (λ U Q {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = U} {θ = seal-name (freshSealName W) ∷ θ}
          {c = c} {V = Q}
          {n = n} {o = o} terminal eq k)
      (λ U′ Q′ {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = U′} {θ = seal-name (freshSealName W′) ∷ θ′}
          {c = c′} {V = Q′}
          {n = n} {o = o} terminal eq k)

paired-instantiation-tail-backward-bundle :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
    {θ θ′ A A′ B B′ C C′ V V′ c c′}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pA⇑ :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {q :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ C ⊑ C′ ⊣ suc Δᴿ}
    {R : WorldRelation W W′} →
  (unique : AssumptionMembershipUnique Φ) →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (lift :
    NTI.LiftStoreⁱ
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′) →
  (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  (allocated :
    RuntimeNarrowing
      (allocate-both R (type-narrowing pA) θ~θ′)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) pA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ)
      (seal-name (freshSealName W′) ∷ θ′)) →
  (action :
    ReachableComponentCoercionNarrowing
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) pA⇑ ∷ ρ′)
      (apply-coercion c) (apply-coercion c′)
      q (⊑-lift∀ᵢ p)) →
  FramedValueNarrowing
    {A = `∀ C} {A′ = `∀ C′}
    {p = ImprecisionWf.∀ⁱ q}
    runtime V V′ →
  FramedDirectionalPairedInstantiateValueSimulation
    backward-direction index →
  FramedDirectionalPairedInstantiateValueSimulation
    target-blame-direction index →
  FramedDirectionalCoercionSimulation
    backward-direction index →
  FramedDirectionalCoercionSimulation
    target-blame-direction index →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ p) R
    (instantiation-tail W θ A c V)
    (instantiation-tail W′ θ′ A′ c′ V′)
    index
  ×
  TargetBlameSimulation R
    (instantiation-tail W θ A c V)
    (instantiation-tail W′ θ′ A′ c′ V′)
    index
paired-instantiation-tail-backward-bundle
    {index} {W} {W′} {ρ = ρ} {ρ′ = ρ′}
    {θ = θ} {θ′ = θ′} {A = A} {A′ = A′}
    {V = V} {V′ = V′} {c = c} {c′ = c′}
    {p = p} {pA = pA} {pA⇑ = pA⇑} {q = q}
    {R = R}
    unique runtime lift θ~θ′ allocated action value
    instantiate-backward instantiate-blame
    coercion-backward coercion-blame =
  backward-extension-base
    {right-index = index}
    {value-result = FramedValueResult ρ θ θ′ p}
    {R = R}
    {S = allocate-both R (type-narrowing pA) θ~θ′}
    {left = instantiation-tail W θ A c V}
    {right = instantiation-tail W′ θ′ A′ c′ V′}
    allocation-extension
    (backward-result-map
      {right-index = index}
      {source-result = lifted-result}
      {target-result = FramedValueResult ρ θ θ′ p}
      {R = allocate-both R (type-narrowing pA) θ~θ′}
      {left = instantiation-tail W θ A c V}
      {right = instantiation-tail W′ θ′ A′ c′ V′}
      chained-backward
      (paired-tail-result
        unique runtime allocation-extension)) ,
  chained-blame
  where
  allocation-extension =
    extension-both extension-refl

  lifted-result =
    FramedValueResult
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) pA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ)
      (seal-name (freshSealName W′) ∷ θ′)
      (⊑-lift∀ᵢ p)

  body-result =
    FramedValueResult
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) pA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ)
      (seal-name (freshSealName W′) ∷ θ′) q

  coerce-left-stable :
    ∀ U Q →
    TerminalStable
      (coerceValue U
        (seal-name (freshSealName W) ∷ θ) c Q)
  coerce-left-stable U Q {n = n} {o = o} =
    coerceValue-terminal-stable
      {W = U} {θ = seal-name (freshSealName W) ∷ θ}
      {c = c} {V = Q} {n = n} {o = o}

  coerce-right-stable :
    ∀ U′ Q′ →
    TerminalStable
      (coerceValue U′
        (seal-name (freshSealName W′) ∷ θ′) c′ Q′)
  coerce-right-stable U′ Q′ {n = n} {o = o} =
    coerceValue-terminal-stable
      {W = U′} {θ = seal-name (freshSealName W′) ∷ θ′}
      {c = c′} {V = Q′} {n = n} {o = o}

  chained-backward =
    directional-chain-backward
      {W = allocate W A θ}
      {W′ = allocate W′ A′ θ′}
      {right-index = index}
      {head-result = body-result}
      {continuation-result = lifted-result}
      {R = allocate-both R (type-narrowing pA) θ~θ′}
      {left-head =
        instantiateValue
          (allocate W A θ) (freshSealName W) V}
      {right-head =
        instantiateValue
          (allocate W′ A′ θ′) (freshSealName W′) V′}
      {left-continuation =
        λ U Q →
          coerceValue U
            (seal-name (freshSealName W) ∷ θ) c Q}
      {right-continuation =
        λ U′ Q′ →
          coerceValue U′
            (seal-name (freshSealName W′) ∷ θ′) c′ Q′}
      (instantiate-backward
        unique runtime lift θ~θ′ allocated value)
      (instantiate-blame
        unique runtime lift θ~θ′ allocated value)
      (λ
        { R≤S (framed-result runtimeS result) →
            coercion-backward
              (assumption-membership-unique-matched unique)
              runtimeS action result
        })
      (λ
        { R≤S (framed-result runtimeS result) →
            coercion-blame
              (assumption-membership-unique-matched unique)
              runtimeS action result
        })
      refl
      (λ U Q → refl)
      (λ { {n} {o} terminal eq k →
        instantiateValue-terminal-stable
          {W = allocate W A θ}
          {α = freshSealName W} {V = V}
          {n = n} {o = o} terminal eq k
        })
      (λ { {n} {o} terminal eq k →
        instantiateValue-terminal-stable
          {W = allocate W′ A′ θ′}
          {α = freshSealName W′} {V = V′}
          {n = n} {o = o} terminal eq k
        })
      coerce-left-stable
      coerce-right-stable

  chained-blame =
    directional-chain-target-blame
      {W = allocate W A θ}
      {W′ = allocate W′ A′ θ′}
      {right-index = index}
      {head-result = body-result}
      {continuation-result = lifted-result}
      {R = allocate-both R (type-narrowing pA) θ~θ′}
      {left-head =
        instantiateValue
          (allocate W A θ) (freshSealName W) V}
      {right-head =
        instantiateValue
          (allocate W′ A′ θ′) (freshSealName W′) V′}
      {left-continuation =
        λ U Q →
          coerceValue U
            (seal-name (freshSealName W) ∷ θ) c Q}
      {right-continuation =
        λ U′ Q′ →
          coerceValue U′
            (seal-name (freshSealName W′) ∷ θ′) c′ Q′}
      (instantiate-backward
        unique runtime lift θ~θ′ allocated value)
      (instantiate-blame
        unique runtime lift θ~θ′ allocated value)
      (λ
        { R≤S (framed-result runtimeS result) →
            coercion-backward
              (assumption-membership-unique-matched unique)
              runtimeS action result
        })
      (λ
        { R≤S (framed-result runtimeS result) →
            coercion-blame
              (assumption-membership-unique-matched unique)
              runtimeS action result
        })
      refl
      (λ U Q → refl)
      (λ { {n} {o} terminal eq k →
        instantiateValue-terminal-stable
          {W = allocate W A θ}
          {α = freshSealName W} {V = V}
          {n = n} {o = o} terminal eq k
        })
      (λ { {n} {o} terminal eq k →
        instantiateValue-terminal-stable
          {W = allocate W′ A′ θ′}
          {α = freshSealName W′} {V = V′}
          {n = n} {o = o} terminal eq k
        })
      coerce-left-stable
      coerce-right-stable
