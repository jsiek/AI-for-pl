module Simulation.Framed.InterpreterFramedSimulationMotive where

-- File Charter:
--   * States the exact runtime-framed motives of the mutual fuel proof.
--   * Indexes returned values by the static precision derivation and runtime
--     frame that produced them.
--   * Keeps paired and one-sided allocation results explicit.
--   * Contains no recursion, interpreter equation, or reduction result.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Simulation.Coercion.InterpreterCoercionSimulationMotive using
  (executeCoercionAction)
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterReachableCoercionNarrowing
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped)
import NuTermImprecision as NTI
import NuTerms as N
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

FramedIndexedCoercionSimulation :
  StepIndex → StepIndex → Set₂
FramedIndexedCoercionSimulation left-index right-index =
  ∀ {W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′ B B′ V V′ left right}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    left right p q →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ q)
    R
    (executeCoercionAction W θ left V)
    (executeCoercionAction W′ θ′ right V′)
    left-index right-index

FramedIndexedApplyValueSimulation :
  StepIndex → StepIndex → Set₂
FramedIndexedApplyValueSimulation left-index right-index =
  ∀ {W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ A A′ B B′ V V′ U U′}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  FramedValueNarrowing
    {A = A ⇒ B} {A′ = A′ ⇒ B′}
    {p = pA ImprecisionWf.↦ pB} runtime V V′ →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = pA} runtime U U′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ pB) R
    (applyValue W V U)
    (applyValue W′ V′ U′)
    left-index right-index

FramedIndexedPairedInstantiateValueSimulation :
  StepIndex → StepIndex → Set₂
FramedIndexedPairedInstantiateValueSimulation
    left-index right-index =
  ∀ {W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        (suc Δᴸ) (suc Δᴿ)}
    {θ θ′ A A′ B B′ V V′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {p⇑ :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ}
    {q :
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
        ⊢ B ⊑ B′ ⊣ suc Δᴿ}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  NTI.LiftStoreⁱ
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  (allocated :
    RuntimeNarrowing
      (allocate-both R (type-narrowing p) θ~θ′)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) p⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ)
      (seal-name (freshSealName W′) ∷ θ′)) →
  FramedValueNarrowing
    {A = `∀ B} {A′ = `∀ B′}
    {p = ImprecisionWf.∀ⁱ q} runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) p⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ)
      (seal-name (freshSealName W′) ∷ θ′)
      q)
    (allocate-both R (type-narrowing p) θ~θ′)
    (instantiateValue
      (allocate W A θ) (freshSealName W) V)
    (instantiateValue
      (allocate W′ A′ θ′) (freshSealName W′) V′)
    left-index right-index

FramedIndexedLeftInstantiateValueSimulation :
  StepIndex → StepIndex → Set₂
FramedIndexedLeftInstantiateValueSimulation
    left-index right-index =
  ∀ {W W′ Φ Δᴸ Δᴿ}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {ρ′ :
      NTI.StoreImp
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ}
    {θ θ′ A B B′ V V′}
    {hA⇑ : WfTy (suc Δᴸ) (⇑ᵗ A)}
    {q :
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ
        ⊢ B ⊑ B′ ⊣ Δᴿ}
    {nonvar : ImprecisionWf.NonVar B}
    {occ : occurs zero B ≡ true}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  NTI.LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  (θ-ok : TypeEnvironmentScoped W θ) →
  (allocated :
    RuntimeNarrowing
      (allocate-left-dynamic {A = A} R θ-ok)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′) →
  FramedValueNarrowing
    {A = `∀ B} {A′ = B′}
    {p = ImprecisionWf.ν nonvar occ q}
    runtime V V′ →
  IndexedTerminalSimulation
    (FramedValueResult
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′ q)
    (allocate-left-dynamic {A = A} R θ-ok)
    (instantiateValue
      (allocate W A θ) (freshSealName W) V)
    (immediateReturn W′ V′)
    left-index right-index

FramedIndexedInterpreterTermSimulation :
  StepIndex →
  StepIndex →
  (Φ : ImpCtx) →
  (Δᴸ Δᴿ : TyCtx) →
  (ρ : NTI.StoreImp Φ Δᴸ Δᴿ) →
  (γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ) →
  (N N′ : N.Term) →
  (A B : Ty) →
  (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  Set₂
FramedIndexedInterpreterTermSimulation
    left-index right-index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p =
  ∀ {W W′ θ θ′ γ γ′}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ p) R
    (interpret W γ θ N)
    (interpret W′ γ′ θ′ N′)
    left-index right-index
