module proof.InterpreterDirectionalZero where

-- File Charter:
--   * Discharges every direction-specific simulation motive at zero fuel.
--   * Uses only the defining zero equations of the direct interpreter.
--   * Contains no recursive call, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans)

open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Simulation.Coercion.InterpreterCoercionSimulationMotive using
  (executeCoercionAction)
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowing using (FramedValueResult)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing using
  (OperationalValueResult)
open import Typing.InterpreterSemanticTypingCore using
  (instantiateSemantic; nominal-type; ⟦_⟧[_])
open import Narrowing.InterpreterOperationalQuotientValueNarrowing
open import Simulation.Coercion.InterpreterOperationalQuotientSimulationMotive
open import Core.InterpreterOutcome using
  (timed≢blamed; timed≢returned)
open import Simulation.Core.InterpreterSimulationResult using
  (Computation; ValueResultRelation; immediateReturn)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
open import proof.InterpreterDirectionalSimulation using
  (zero-backward; zero-forward; zero-target-blame)

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

operational-zero-forward :
  ∀ {W W′ U A A′}
    {R : WorldRelation W W′}
    {left right : Computation} →
  left zero ≡ timed U →
  ForwardReturnSimulation
    (OperationalValueResult A A′) R left right zero
operational-zero-forward left-zero eq =
  ⊥-elim (timed≢returned (trans (sym left-zero) eq))

operational-zero-backward :
  ∀ {W W′ U′ A A′}
    {R : WorldRelation W W′}
    {left right : Computation} →
  right zero ≡ timed U′ →
  BackwardReturnSimulation
    (OperationalValueResult A A′) R left right zero
operational-zero-backward right-zero eq =
  ⊥-elim (timed≢returned (trans (sym right-zero) eq))

execute-action-zero :
  ∀ {W θ action V} →
  executeCoercionAction W θ action V zero ≡ timed W
execute-action-zero {action = skip-coercion} =
  refl
execute-action-zero {action = apply-coercion c} =
  refl

coercion-forward-zero :
  DirectionalCoercionSimulation forward-direction zero
coercion-forward-zero
    {W} {W′} {θ = θ} {θ′} {B = B} {B′} {V = V} {V′}
    {left = left} {right = right} {R = R}
    runtime action value =
  operational-zero-forward
    {W = W} {W′ = W′} {R = R}
    {left = executeCoercionAction W θ left V}
    {right = executeCoercionAction W′ θ′ right V′}
    (execute-action-zero
      {W = W} {θ = θ} {action = left} {V = V})

coercion-backward-zero :
  DirectionalCoercionSimulation backward-direction zero
coercion-backward-zero
    {W} {W′} {θ = θ} {θ′} {B = B} {B′} {V = V} {V′}
    {left = left} {right = right} {R = R}
    runtime action value =
  operational-zero-backward
    {W = W} {W′ = W′} {R = R}
    {left = executeCoercionAction W θ left V}
    {right = executeCoercionAction W′ θ′ right V′}
    (execute-action-zero
      {W = W′} {θ = θ′} {action = right} {V = V′})

coercion-target-blame-zero :
  DirectionalCoercionSimulation target-blame-direction zero
coercion-target-blame-zero
    {W} {W′} {θ = θ} {θ′} {V = V} {V′}
    {left = left} {right = right} {R = R}
    runtime action value =
  zero-target-blame
    {W = W} {W′ = W′} {R = R}
    {left = executeCoercionAction W θ left V}
    {right = executeCoercionAction W′ θ′ right V′}
    (execute-action-zero
      {W = W′} {θ = θ′} {action = right} {V = V′})

apply-forward-zero :
  DirectionalApplyValueSimulation forward-direction zero
apply-forward-zero
    {W} {W′} {B = B} {B′} {V = V} {V′} {U} {U′} {R = R}
    value argument =
  operational-zero-forward
    {W = W} {W′ = W′} {R = R}
    {left = applyValue W V U} {right = applyValue W′ V′ U′}
    refl

apply-backward-zero :
  DirectionalApplyValueSimulation backward-direction zero
apply-backward-zero
    {W} {W′} {B = B} {B′} {V = V} {V′} {U} {U′} {R = R}
    value argument =
  operational-zero-backward
    {W = W} {W′ = W′} {R = R}
    {left = applyValue W V U} {right = applyValue W′ V′ U′}
    refl

apply-target-blame-zero :
  DirectionalApplyValueSimulation target-blame-direction zero
apply-target-blame-zero
    {W} {W′} {V = V} {V′} {U} {U′} {R = R}
    value argument =
  zero-target-blame
    {W = W} {W′ = W′} {R = R}
    {left = applyValue W V U} {right = applyValue W′ V′ U′}
    refl

paired-instantiation-forward-zero :
  DirectionalPairedInstantiateValueSimulation forward-direction zero
paired-instantiation-forward-zero
    {W} {W′} {A = A} {A′} {θ} {θ′} {body} {body′}
    {V = V} {V′} {R = R}
    A~A′ θ~θ′ W⊢ W′⊢ value =
  operational-zero-forward
    {W = allocate W A θ} {W′ = allocate W′ A′ θ′}
    {R = allocate-both R A~A′ θ~θ′}
    {left = instantiateValue (allocate W A θ) (freshSealName W) V}
    {right =
      instantiateValue (allocate W′ A′ θ′) (freshSealName W′) V′}
    refl

paired-instantiation-backward-zero :
  DirectionalPairedInstantiateValueSimulation backward-direction zero
paired-instantiation-backward-zero
    {W} {W′} {A = A} {A′} {θ} {θ′} {body} {body′}
    {V = V} {V′} {R = R}
    A~A′ θ~θ′ W⊢ W′⊢ value =
  operational-zero-backward
    {W = allocate W A θ} {W′ = allocate W′ A′ θ′}
    {R = allocate-both R A~A′ θ~θ′}
    {left = instantiateValue (allocate W A θ) (freshSealName W) V}
    {right =
      instantiateValue (allocate W′ A′ θ′) (freshSealName W′) V′}
    refl

paired-instantiation-target-blame-zero :
  DirectionalPairedInstantiateValueSimulation target-blame-direction zero
paired-instantiation-target-blame-zero
    {W} {W′} {A = A} {A′} {θ} {θ′} {V = V} {V′} {R = R}
    A~A′ θ~θ′ W⊢ W′⊢ value =
  zero-target-blame
    {W = allocate W A θ} {W′ = allocate W′ A′ θ′}
    {R = allocate-both R A~A′ θ~θ′}
    {left = instantiateValue (allocate W A θ) (freshSealName W) V}
    {right =
      instantiateValue (allocate W′ A′ θ′) (freshSealName W′) V′}
    refl

left-instantiation-forward-zero :
  DirectionalLeftInstantiateValueSimulation forward-direction zero
left-instantiation-forward-zero
    {W} {W′} {A = A} {θ} {body} {target}
    {V = V} {V′} {R = R}
    θ-ok W⊢ W′⊢ value =
  operational-zero-forward
    {W = allocate W A θ} {W′ = W′}
    {R = allocate-left-dynamic {A = A} R θ-ok}
    {left = instantiateValue (allocate W A θ) (freshSealName W) V}
    {right = immediateReturn W′ V′}
    refl

left-instantiation-backward-zero :
  DirectionalLeftInstantiateValueSimulation backward-direction zero
left-instantiation-backward-zero
    {W} {W′} {A = A} {θ} {body} {target}
    {V = V} {V′} {R = R}
    θ-ok W⊢ W′⊢ value =
  operational-zero-backward
    {W = allocate W A θ} {W′ = W′}
    {R = allocate-left-dynamic {A = A} R θ-ok}
    {left = instantiateValue (allocate W A θ) (freshSealName W) V}
    {right = immediateReturn W′ V′}
    refl

left-instantiation-target-blame-zero :
  DirectionalLeftInstantiateValueSimulation target-blame-direction zero
left-instantiation-target-blame-zero
    {W} {W′} {A = A} {θ} {V = V} {V′} {R = R}
    θ-ok W⊢ W′⊢ value =
  zero-target-blame
    {W = allocate W A θ} {W′ = W′}
    {R = allocate-left-dynamic {A = A} R θ-ok}
    {left = instantiateValue (allocate W A θ) (freshSealName W) V}
    {right = immediateReturn W′ V′}
    refl

right-instantiation-forward-zero :
  DirectionalRightInstantiateValueSimulation forward-direction zero
right-instantiation-forward-zero
    {W} {W′} {A′} {θ′} {source} {body′}
    {V = V} {V′} {R = R}
    θ′-ok W⊢ W′⊢ value =
  operational-zero-forward
    {W = W} {W′ = allocate W′ A′ θ′}
    {R = allocate-right-only {A′ = A′} R θ′-ok}
    {left = immediateReturn W V}
    {right =
      instantiateValue (allocate W′ A′ θ′) (freshSealName W′) V′}
    refl

right-instantiation-backward-zero :
  DirectionalRightInstantiateValueSimulation backward-direction zero
right-instantiation-backward-zero
    {W} {W′} {A′} {θ′} {source} {body′}
    {V = V} {V′} {R = R}
    θ′-ok W⊢ W′⊢ value =
  operational-zero-backward
    {W = W} {W′ = allocate W′ A′ θ′}
    {R = allocate-right-only {A′ = A′} R θ′-ok}
    {left = immediateReturn W V}
    {right =
      instantiateValue (allocate W′ A′ θ′) (freshSealName W′) V′}
    refl

right-instantiation-target-blame-zero :
  DirectionalRightInstantiateValueSimulation target-blame-direction zero
right-instantiation-target-blame-zero
    {W} {W′} {A′} {θ′} {V = V} {V′} {R = R}
    θ′-ok W⊢ W′⊢ value =
  zero-target-blame
    {W = W} {W′ = allocate W′ A′ θ′}
    {R = allocate-right-only {A′ = A′} R θ′-ok}
    {left = immediateReturn W V}
    {right =
      instantiateValue (allocate W′ A′ θ′) (freshSealName W′) V′}
    refl

quotient-down-forward-zero :
  DirectionalQuotientDownSimulation forward-direction zero
quotient-down-forward-zero
    unique runtime down value eq =
  ⊥-elim (timed≢returned eq)

quotient-down-backward-zero :
  DirectionalQuotientDownSimulation backward-direction zero
quotient-down-backward-zero
    unique runtime down value eq =
  ⊥-elim (timed≢returned eq)

quotient-down-target-blame-zero :
  DirectionalQuotientDownSimulation target-blame-direction zero
quotient-down-target-blame-zero
    unique runtime down value eq =
  ⊥-elim (timed≢blamed eq)

quotient-up-forward-zero :
  DirectionalQuotientUpSimulation forward-direction zero
quotient-up-forward-zero
    unique up value eq =
  ⊥-elim (timed≢returned eq)

quotient-up-backward-zero :
  DirectionalQuotientUpSimulation backward-direction zero
quotient-up-backward-zero
    unique up value eq =
  ⊥-elim (timed≢returned eq)

quotient-up-target-blame-zero :
  DirectionalQuotientUpSimulation target-blame-direction zero
quotient-up-target-blame-zero
    unique up value eq =
  ⊥-elim (timed≢blamed eq)

framed-coercion-forward-zero :
  FramedDirectionalCoercionSimulation forward-direction zero
framed-coercion-forward-zero
    {W} {W′} {ρ = ρ} {θ} {θ′} {V = V} {V′}
    {left = left} {right = right} {q = q} {R = R}
    unique runtime action value =
  zero-forward
    {W = W} {W′ = W′}
    {value-result = FramedValueResult ρ θ θ′ q} {R = R}
    {left = executeCoercionAction W θ left V}
    {right = executeCoercionAction W′ θ′ right V′}
    (execute-action-zero
      {W = W} {θ = θ} {action = left} {V = V})

framed-coercion-backward-zero :
  FramedDirectionalCoercionSimulation backward-direction zero
framed-coercion-backward-zero
    {W} {W′} {ρ = ρ} {θ} {θ′} {V = V} {V′}
    {left = left} {right = right} {q = q} {R = R}
    unique runtime action value =
  zero-backward
    {W = W} {W′ = W′}
    {value-result = FramedValueResult ρ θ θ′ q} {R = R}
    {left = executeCoercionAction W θ left V}
    {right = executeCoercionAction W′ θ′ right V′}
    (execute-action-zero
      {W = W′} {θ = θ′} {action = right} {V = V′})

framed-coercion-target-blame-zero :
  FramedDirectionalCoercionSimulation target-blame-direction zero
framed-coercion-target-blame-zero
    {W} {W′} {θ = θ} {θ′} {V = V} {V′}
    {left = left} {right = right} {R = R}
    unique runtime action value =
  zero-target-blame
    {W = W} {W′ = W′} {R = R}
    {left = executeCoercionAction W θ left V}
    {right = executeCoercionAction W′ θ′ right V′}
    (execute-action-zero
      {W = W′} {θ = θ′} {action = right} {V = V′})

framed-coercion-backward-bundle-zero :
  FramedDirectionalCoercionSimulation backward-direction zero
  × FramedDirectionalCoercionSimulation target-blame-direction zero
framed-coercion-backward-bundle-zero =
  framed-coercion-backward-zero ,
  framed-coercion-target-blame-zero

framed-apply-forward-zero :
  FramedDirectionalApplyValueSimulation forward-direction zero
framed-apply-forward-zero
    {W} {W′} {ρ = ρ} {θ} {θ′} {V = V} {V′} {U} {U′}
    {pB = pB} {R = R}
    unique runtime value argument =
  zero-forward
    {W = W} {W′ = W′}
    {value-result = FramedValueResult ρ θ θ′ pB} {R = R}
    {left = applyValue W V U} {right = applyValue W′ V′ U′}
    refl

framed-apply-backward-zero :
  FramedDirectionalApplyValueSimulation backward-direction zero
framed-apply-backward-zero
    {W} {W′} {ρ = ρ} {θ} {θ′} {V = V} {V′} {U} {U′}
    {pB = pB} {R = R}
    unique runtime value argument =
  zero-backward
    {W = W} {W′ = W′}
    {value-result = FramedValueResult ρ θ θ′ pB} {R = R}
    {left = applyValue W V U} {right = applyValue W′ V′ U′}
    refl

framed-apply-target-blame-zero :
  FramedDirectionalApplyValueSimulation target-blame-direction zero
framed-apply-target-blame-zero
    {W} {W′} {V = V} {V′} {U} {U′} {R = R}
    unique runtime value argument =
  zero-target-blame
    {W = W} {W′ = W′} {R = R}
    {left = applyValue W V U} {right = applyValue W′ V′ U′}
    refl

framed-apply-backward-bundle-zero :
  FramedDirectionalApplyValueSimulation backward-direction zero
  × FramedDirectionalApplyValueSimulation target-blame-direction zero
framed-apply-backward-bundle-zero =
  framed-apply-backward-zero ,
  framed-apply-target-blame-zero

framed-paired-instantiation-forward-zero :
  FramedDirectionalPairedInstantiateValueSimulation
    forward-direction zero
framed-paired-instantiation-forward-zero
    {W} {W′} {ρ′ = ρ′} {θ} {θ′}
    {A} {A′} {V = V} {V′} {p = p} {p⇑ = p⇑}
    {q = q} {R = R}
    unique runtime lift θ~θ′ allocated value =
  zero-forward
    {W = allocate W A θ} {W′ = allocate W′ A′ θ′}
    {value-result =
      FramedValueResult
        (NTI.store-matched zero _ zero _ p⇑ ∷ ρ′)
        (seal-name (freshSealName W) ∷ θ)
        (seal-name (freshSealName W′) ∷ θ′) q}
    {R = allocate-both R (type-narrowing p) θ~θ′}
    {left = instantiateValue (allocate W A θ) (freshSealName W) V}
    {right =
      instantiateValue (allocate W′ A′ θ′) (freshSealName W′) V′}
    refl

framed-paired-instantiation-backward-zero :
  FramedDirectionalPairedInstantiateValueSimulation
    backward-direction zero
framed-paired-instantiation-backward-zero
    {W} {W′} {ρ′ = ρ′} {θ} {θ′}
    {A} {A′} {V = V} {V′} {p = p} {p⇑ = p⇑}
    {q = q} {R = R}
    unique runtime lift θ~θ′ allocated value =
  zero-backward
    {W = allocate W A θ} {W′ = allocate W′ A′ θ′}
    {value-result =
      FramedValueResult
        (NTI.store-matched zero _ zero _ p⇑ ∷ ρ′)
        (seal-name (freshSealName W) ∷ θ)
        (seal-name (freshSealName W′) ∷ θ′) q}
    {R = allocate-both R (type-narrowing p) θ~θ′}
    {left = instantiateValue (allocate W A θ) (freshSealName W) V}
    {right =
      instantiateValue (allocate W′ A′ θ′) (freshSealName W′) V′}
    refl

framed-paired-instantiation-target-blame-zero :
  FramedDirectionalPairedInstantiateValueSimulation
    target-blame-direction zero
framed-paired-instantiation-target-blame-zero
    {W} {W′} {θ = θ} {θ′} {A = A} {A′}
    {V = V} {V′} {p = p} {R = R}
    unique runtime lift θ~θ′ allocated value =
  zero-target-blame
    {W = allocate W A θ} {W′ = allocate W′ A′ θ′}
    {R = allocate-both R (type-narrowing p) θ~θ′}
    {left = instantiateValue (allocate W A θ) (freshSealName W) V}
    {right =
      instantiateValue (allocate W′ A′ θ′) (freshSealName W′) V′}
    refl

framed-left-instantiation-forward-zero :
  FramedDirectionalLeftInstantiateValueSimulation
    forward-direction zero
framed-left-instantiation-forward-zero
    {W} {W′} {ρ′ = ρ′} {θ} {θ′} {A} {V = V} {V′}
    {hA⇑ = hA⇑} {q = q} {R = R}
    unique runtime lift θ-ok allocated value =
  zero-forward
    {W = allocate W A θ} {W′ = W′}
    {value-result =
      FramedValueResult
        (NTI.store-left zero _ hA⇑ ∷ ρ′)
        (seal-name (freshSealName W) ∷ θ) θ′ q}
    {R = allocate-left-dynamic {A = A} R θ-ok}
    {left = instantiateValue (allocate W A θ) (freshSealName W) V}
    {right = immediateReturn W′ V′}
    refl

framed-left-instantiation-backward-zero :
  FramedDirectionalLeftInstantiateValueSimulation
    backward-direction zero
framed-left-instantiation-backward-zero
    {W} {W′} {ρ′ = ρ′} {θ} {θ′} {A} {V = V} {V′}
    {hA⇑ = hA⇑} {q = q} {R = R}
    unique runtime lift θ-ok allocated value =
  zero-backward
    {W = allocate W A θ} {W′ = W′}
    {value-result =
      FramedValueResult
        (NTI.store-left zero _ hA⇑ ∷ ρ′)
        (seal-name (freshSealName W) ∷ θ) θ′ q}
    {R = allocate-left-dynamic {A = A} R θ-ok}
    {left = instantiateValue (allocate W A θ) (freshSealName W) V}
    {right = immediateReturn W′ V′}
    refl

framed-left-instantiation-target-blame-zero :
  FramedDirectionalLeftInstantiateValueSimulation
    target-blame-direction zero
framed-left-instantiation-target-blame-zero
    {W} {W′} {θ = θ} {A = A} {V = V} {V′} {R = R}
    unique runtime lift θ-ok allocated value =
  zero-target-blame
    {W = allocate W A θ} {W′ = W′}
    {R = allocate-left-dynamic {A = A} R θ-ok}
    {left = instantiateValue (allocate W A θ) (freshSealName W) V}
    {right = immediateReturn W′ V′}
    refl

framed-term-forward-zero :
  ∀ {Φ Δᴸ Δᴿ ρ γ N N′ A B p} →
  FramedDirectionalInterpreterTermSimulation
    forward-direction zero Φ Δᴸ Δᴿ ρ γ N N′ A B p
framed-term-forward-zero
    {ρ = ρ} {N = N} {N′} {p = p}
    {W} {W′} {θ} {θ′} {γ = γ} {γ′} {R = R}
    unique runtime environment origins terms =
  zero-forward
    {W = W} {W′ = W′}
    {value-result = FramedValueResult ρ θ θ′ p} {R = R}
    {left = interpret W γ θ N} {right = interpret W′ γ′ θ′ N′}
    refl

framed-term-backward-zero :
  ∀ {Φ Δᴸ Δᴿ ρ γ N N′ A B p} →
  FramedDirectionalInterpreterTermSimulation
    backward-direction zero Φ Δᴸ Δᴿ ρ γ N N′ A B p
framed-term-backward-zero
    {ρ = ρ} {N = N} {N′} {p = p}
    {W} {W′} {θ} {θ′} {γ = γ} {γ′} {R = R}
    unique runtime environment origins terms =
  zero-backward
    {W = W} {W′ = W′}
    {value-result = FramedValueResult ρ θ θ′ p} {R = R}
    {left = interpret W γ θ N} {right = interpret W′ γ′ θ′ N′}
    refl

framed-term-target-blame-zero :
  ∀ {Φ Δᴸ Δᴿ ρ γ N N′ A B p} →
  FramedDirectionalInterpreterTermSimulation
    target-blame-direction zero Φ Δᴸ Δᴿ ρ γ N N′ A B p
framed-term-target-blame-zero
    {N = N} {N′} {p = p}
    {W} {W′} {θ = θ} {θ′} {γ = γ} {γ′} {R = R}
    unique runtime environment origins terms =
  zero-target-blame
    {W = W} {W′ = W′} {R = R}
    {left = interpret W γ θ N} {right = interpret W′ γ′ θ′ N′}
    refl

framed-term-backward-bundle-zero :
  ∀ {Φ Δᴸ Δᴿ ρ γ N N′ A B p} →
  FramedDirectionalInterpreterTermSimulation
    backward-direction zero Φ Δᴸ Δᴿ ρ γ N N′ A B p
  ×
  FramedDirectionalInterpreterTermSimulation
    target-blame-direction zero Φ Δᴸ Δᴿ ρ γ N N′ A B p
framed-term-backward-bundle-zero =
  framed-term-backward-zero , framed-term-target-blame-zero
