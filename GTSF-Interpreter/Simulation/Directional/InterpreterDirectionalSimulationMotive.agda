module Simulation.Directional.InterpreterDirectionalSimulationMotive where

-- File Charter:
--   * States the direction-specific motives of the constructive fuel driver.
--   * Separates forward return from the mutually supporting backward-return
--     and target-blame observations.
--   * Retains exact static/runtime value frames and one-sided allocation
--     relations.
--   * Contains no recursion, interpreter equation, or reduction result.

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
import Level
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
import Narrowing.InterpreterOperationalValueNarrowing as Operational
open import Typing.InterpreterSemanticTypingCore using
  ( WorldTyping
  ; _⇒ᵛ_
  ; instantiateSemantic
  ; nominal-type
  ; polymorphic-type
  ; ⟦_⟧[_]
  )
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

DirectionalCoercionSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
DirectionalCoercionSimulation direction index =
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ A A′ B B′ p q V V′ left right}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ
    left right {A} {A′} {B} {B′} p q →
  Operational.OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
  DirectionalObservation direction
    (Operational.OperationalValueResult
      ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (executeCoercionAction W θ left V)
    (executeCoercionAction W′ θ′ right V′)
    index

DirectionalApplyValueSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
DirectionalApplyValueSimulation direction index =
  ∀ {W W′ A A′ B B′ V V′ U U′}
    {R : WorldRelation W W′} →
  Operational.OperationalValueNarrowing
    (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′ →
  Operational.OperationalValueNarrowing
    A A′ R U U′ →
  DirectionalObservation direction
    (Operational.OperationalValueResult B B′)
    R
    (applyValue W V U)
    (applyValue W′ V′ U′)
    index

DirectionalPairedInstantiateValueSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
DirectionalPairedInstantiateValueSimulation direction index =
  ∀ {W W′ A A′ θ θ′ body body′ V V′}
    {R : WorldRelation W W′} →
  (A~A′ : InterpreterTypeNarrowing A A′) →
  (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  WorldTyping (allocate W A θ) →
  WorldTyping (allocate W′ A′ θ′) →
  Operational.OperationalValueNarrowing
    (polymorphic-type body) (polymorphic-type body′) R V V′ →
  DirectionalObservation direction
    (Operational.OperationalValueResult
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W))) body)
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W′))) body′))
    (allocate-both R A~A′ θ~θ′)
    (instantiateValue
      (allocate W A θ) (freshSealName W) V)
    (instantiateValue
      (allocate W′ A′ θ′) (freshSealName W′) V′)
    index

DirectionalLeftInstantiateValueSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
DirectionalLeftInstantiateValueSimulation direction index =
  ∀ {W W′ A θ body target V V′}
    {R : WorldRelation W W′} →
  (θ-ok : TypeEnvironmentScoped W θ) →
  WorldTyping (allocate W A θ) →
  WorldTyping W′ →
  Operational.OperationalValueNarrowing
    (polymorphic-type body) target R V V′ →
  DirectionalObservation direction
    (Operational.OperationalValueResult
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W))) body)
      target)
    (allocate-left-dynamic {A = A} R θ-ok)
    (instantiateValue
      (allocate W A θ) (freshSealName W) V)
    (immediateReturn W′ V′)
    index

DirectionalRightInstantiateValueSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
DirectionalRightInstantiateValueSimulation direction index =
  ∀ {W W′ A′ θ′ source body′ V V′}
    {R : WorldRelation W W′} →
  (θ′-ok : TypeEnvironmentScoped W′ θ′) →
  WorldTyping W →
  WorldTyping (allocate W′ A′ θ′) →
  Operational.OperationalValueNarrowing
    source (polymorphic-type body′) R V V′ →
  DirectionalObservation direction
    (Operational.OperationalValueResult
      source
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W′))) body′))
    (allocate-right-only {A′ = A′} R θ′-ok)
    (immediateReturn W V)
    (instantiateValue
      (allocate W′ A′ θ′) (freshSealName W′) V′)
    index

DirectionalInterpreterTermSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  (Φ : ImpCtx) →
  (Δᴸ Δᴿ : TyCtx) →
  (ρ : NTI.StoreImp Φ Δᴸ Δᴿ) →
  (γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ) →
  (N N′ : N.Term) →
  (A B : Ty) →
  (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
DirectionalInterpreterTermSimulation
    direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p =
  ∀ {W W′ θ θ′ γ γ′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  Operational.OperationalEnvironmentNarrowing
    θ θ′ R γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  DirectionalObservation direction
    (Operational.OperationalValueResult
      ⟦ A ⟧[ θ ] ⟦ B ⟧[ θ′ ])
    R
    (interpret W γ θ N)
    (interpret W′ γ′ θ′ N′)
    index

FramedDirectionalCoercionSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
FramedDirectionalCoercionSimulation direction index =
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
  DirectionalObservation direction
    (FramedValueResult ρ θ θ′ q) R
    (executeCoercionAction W θ left V)
    (executeCoercionAction W′ θ′ right V′)
    index

FramedDirectionalApplyValueSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
FramedDirectionalApplyValueSimulation direction index =
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
  DirectionalObservation direction
    (FramedValueResult ρ θ θ′ pB) R
    (applyValue W V U)
    (applyValue W′ V′ U′)
    index

FramedDirectionalPairedInstantiateValueSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
FramedDirectionalPairedInstantiateValueSimulation direction index =
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
  DirectionalObservation direction
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
    index

FramedDirectionalLeftInstantiateValueSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
FramedDirectionalLeftInstantiateValueSimulation direction index =
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
  DirectionalObservation direction
    (FramedValueResult
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName W) ∷ θ) θ′ q)
    (allocate-left-dynamic {A = A} R θ-ok)
    (instantiateValue
      (allocate W A θ) (freshSealName W) V)
    (immediateReturn W′ V′)
    index

FramedDirectionalInterpreterTermSimulation :
  (direction : TerminalDirection) →
  StepIndex →
  (Φ : ImpCtx) →
  (Δᴸ Δᴿ : TyCtx) →
  (ρ : NTI.StoreImp Φ Δᴸ Δᴿ) →
  (γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ) →
  (N N′ : N.Term) →
  (A B : Ty) →
  (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  Set (Level.suc Level.zero Level.⊔ direction-level direction)
FramedDirectionalInterpreterTermSimulation
    direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p =
  ∀ {W W′ θ θ′ γ γ′}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  DirectionalObservation direction
    (FramedValueResult ρ θ θ′ p) R
    (interpret W γ θ N)
    (interpret W′ γ′ θ′ N′)
    index
