module proof.InterpreterDirectionalFramedLeftInstantiationTail where

-- File Charter:
--   * Composes source-only semantic instantiation with its reveal coercion
--     while the target value remains an immediate return.
--   * Removes the source allocation frame and rebases the result at the
--     pre-allocation relation in all three terminal directions.
--   * Contains no recursive definition, reduction, or catch-up theorem.

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; _,_)

open import ImprecisionWf using
  (NonVar; _ˣ⊑★; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterReachableCoercionNarrowing
open import Core.InterpreterFuel using
  (coerceValue-terminal-stable; instantiateValue-terminal-stable)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using
  (TerminalStable; immediateReturn)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped)
import NuTermImprecision as NTI
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  (assumption-membership-unique-source)
open import proof.InterpreterDirectionalFramedInstantiationTailResult using
  (left-tail-result)
open import proof.InterpreterDirectionalSequence using
  ( directional-left-chain-backward
  ; directional-left-chain-forward
  ; directional-left-chain-target-blame
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
  (⊑-source-liftνᵢ)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

left-instantiation-tail-forward :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ}
    {θ θ′ A B B′ C V V′ c}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {hA⇑ : WfTy (suc Δᴸ) (⇑ᵗ A)}
    {q :
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ
        ⊢ C ⊑ B′ ⊣ Δᴿ}
    {nonvar : NonVar C}
    {occ : occurs zero C ≡ true}
    {R : WorldRelation W W′} →
  (unique : AssumptionMembershipUnique Φ) →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (lift :
    NTI.LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  (θ-ok : TypeEnvironmentScoped W θ) →
  (allocated :
    RuntimeNarrowing
      (allocate-left-dynamic {A = A} R θ-ok)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′) →
  (action :
    ReachableComponentCoercionNarrowing
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (apply-coercion c) skip-coercion
      q (⊑-source-liftνᵢ p)) →
  FramedValueNarrowing
    {A = `∀ C} {A′ = B′}
    {p = ImprecisionWf.ν nonvar occ q}
    runtime V V′ →
  FramedDirectionalLeftInstantiateValueSimulation
    forward-direction index →
  FramedDirectionalCoercionSimulation
    forward-direction index →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ p) R
    (instantiation-tail W θ A c V)
    (immediateReturn W′ V′)
    index
left-instantiation-tail-forward
    {index} {W} {W′} {ρ = ρ} {ρ′ = ρ′}
    {θ = θ} {θ′ = θ′} {A = A}
    {V = V} {V′ = V′} {c = c}
    {p = p} {hA⇑ = hA⇑} {q = q} {R = R}
    unique runtime lift θ-ok allocated action value
    instantiate coercion =
  forward-extension-base
    {left-index = index}
    {value-result = FramedValueResult ρ θ θ′ p}
    {R = R}
    {S = allocate-left-dynamic {A = A} R θ-ok}
    {left = instantiation-tail W θ A c V}
    {right = immediateReturn W′ V′}
    allocation-extension
    (forward-result-map
      {left-index = index}
      {source-result = lifted-result}
      {target-result = FramedValueResult ρ θ θ′ p}
      {R = allocate-left-dynamic {A = A} R θ-ok}
      {left = instantiation-tail W θ A c V}
      {right = immediateReturn W′ V′}
      chained
      (left-tail-result
        unique runtime allocation-extension))
  where
  allocation-extension =
    extension-left extension-refl

  lifted-result =
    FramedValueResult
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′
      (⊑-source-liftνᵢ p)

  body-result =
    FramedValueResult
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′ q

  chained =
    directional-left-chain-forward
      {W = allocate W A θ}
      {W′ = W′}
      {left-index = index}
      {head-result = body-result}
      {continuation-result = lifted-result}
      {R = allocate-left-dynamic {A = A} R θ-ok}
      {left-head =
        instantiateValue
          (allocate W A θ) (freshSealName W) V}
      {right-head = immediateReturn W′ V′}
      {left-continuation =
        λ U Q →
          coerceValue U
            (seal-name (freshSealName W) ∷ θ) c Q}
      (instantiate unique runtime lift θ-ok allocated value)
      (λ
        { R≤S (framed-result runtimeS result) →
            coercion
              (assumption-membership-unique-source unique)
              runtimeS action result
        })
      refl
      (λ { {n} {o} terminal eq k →
        instantiateValue-terminal-stable
          {W = allocate W A θ}
          {α = freshSealName W} {V = V}
          {n = n} {o = o} terminal eq k
        })
      (λ U Q {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = U} {θ = seal-name (freshSealName W) ∷ θ}
          {c = c} {V = Q}
          {n = n} {o = o} terminal eq k)

left-instantiation-tail-backward-bundle :
  ∀ {index W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ}
    {θ θ′ A B B′ C V V′ c}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {hA⇑ : WfTy (suc Δᴸ) (⇑ᵗ A)}
    {q :
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ
        ⊢ C ⊑ B′ ⊣ Δᴿ}
    {nonvar : NonVar C}
    {occ : occurs zero C ≡ true}
    {R : WorldRelation W W′} →
  (unique : AssumptionMembershipUnique Φ) →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (lift :
    NTI.LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′) →
  (θ-ok : TypeEnvironmentScoped W θ) →
  (allocated :
    RuntimeNarrowing
      (allocate-left-dynamic {A = A} R θ-ok)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′) →
  (action :
    ReachableComponentCoercionNarrowing
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (apply-coercion c) skip-coercion
      q (⊑-source-liftνᵢ p)) →
  FramedValueNarrowing
    {A = `∀ C} {A′ = B′}
    {p = ImprecisionWf.ν nonvar occ q}
    runtime V V′ →
  FramedDirectionalLeftInstantiateValueSimulation
    backward-direction index →
  FramedDirectionalLeftInstantiateValueSimulation
    target-blame-direction index →
  FramedDirectionalCoercionSimulation
    backward-direction index →
  FramedDirectionalCoercionSimulation
    target-blame-direction index →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ p) R
    (instantiation-tail W θ A c V)
    (immediateReturn W′ V′)
    index
  ×
  TargetBlameSimulation R
    (instantiation-tail W θ A c V)
    (immediateReturn W′ V′)
    index
left-instantiation-tail-backward-bundle
    {index} {W} {W′} {ρ = ρ} {ρ′ = ρ′}
    {θ = θ} {θ′ = θ′} {A = A}
    {V = V} {V′ = V′} {c = c}
    {p = p} {hA⇑ = hA⇑} {q = q} {R = R}
    unique runtime lift θ-ok allocated action value
    instantiate-backward instantiate-blame
    coercion-backward coercion-blame =
  backward-extension-base
    {right-index = index}
    {value-result = FramedValueResult ρ θ θ′ p}
    {R = R}
    {S = allocate-left-dynamic {A = A} R θ-ok}
    {left = instantiation-tail W θ A c V}
    {right = immediateReturn W′ V′}
    allocation-extension
    (backward-result-map
      {right-index = index}
      {source-result = lifted-result}
      {target-result = FramedValueResult ρ θ θ′ p}
      {R = allocate-left-dynamic {A = A} R θ-ok}
      {left = instantiation-tail W θ A c V}
      {right = immediateReturn W′ V′}
      chained-backward
      (left-tail-result
        unique runtime allocation-extension)) ,
  chained-blame
  where
  allocation-extension =
    extension-left extension-refl

  lifted-result =
    FramedValueResult
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′
      (⊑-source-liftνᵢ p)

  body-result =
    FramedValueResult
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′ q

  coerce-left-stable :
    ∀ U Q →
    TerminalStable
      (coerceValue U
        (seal-name (freshSealName W) ∷ θ) c Q)
  coerce-left-stable U Q {n = n} {o = o} =
    coerceValue-terminal-stable
      {W = U} {θ = seal-name (freshSealName W) ∷ θ}
      {c = c} {V = Q} {n = n} {o = o}

  chained-backward =
    directional-left-chain-backward
      {W = allocate W A θ}
      {W′ = W′}
      {right-index = index}
      {head-result = body-result}
      {continuation-result = lifted-result}
      {R = allocate-left-dynamic {A = A} R θ-ok}
      {left-head =
        instantiateValue
          (allocate W A θ) (freshSealName W) V}
      {right-head = immediateReturn W′ V′}
      {left-continuation =
        λ U Q →
          coerceValue U
            (seal-name (freshSealName W) ∷ θ) c Q}
      (instantiate-backward
        unique runtime lift θ-ok allocated value)
      (instantiate-blame
        unique runtime lift θ-ok allocated value)
      (λ
        { R≤S (framed-result runtimeS result) →
            coercion-backward
              (assumption-membership-unique-source unique)
              runtimeS action result
        })
      (λ
        { R≤S (framed-result runtimeS result) →
            coercion-blame
              (assumption-membership-unique-source unique)
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
      coerce-left-stable
      refl

  chained-blame =
    directional-left-chain-target-blame
      {W = allocate W A θ}
      {W′ = W′}
      {right-index = index}
      {head-result = body-result}
      {continuation-result = lifted-result}
      {R = allocate-left-dynamic {A = A} R θ-ok}
      {left-head =
        instantiateValue
          (allocate W A θ) (freshSealName W) V}
      {right-head = immediateReturn W′ V′}
      {left-continuation =
        λ U Q →
          coerceValue U
            (seal-name (freshSealName W) ∷ θ) c Q}
      (instantiate-backward
        unique runtime lift θ-ok allocated value)
      (instantiate-blame
        unique runtime lift θ-ok allocated value)
      (λ
        { R≤S (framed-result runtimeS result) →
            coercion-backward
              (assumption-membership-unique-source unique)
              runtimeS action result
        })
      (λ
        { R≤S (framed-result runtimeS result) →
            coercion-blame
              (assumption-membership-unique-source unique)
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
      coerce-left-stable
      refl
