module Narrowing.InterpreterFramedValueNarrowingProperties where

-- File Charter:
--   * Public structural interface for exact runtime-framed value narrowing.
--   * Exposes related-world weakening and erasure to the public value
--     relation used by `Joined`.
--   * Delegates exhaustive recursion to a reduction-free proof module.

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterFramedValueNarrowing
open import Narrowing.InterpreterOperationalValueNarrowing using
  (OperationalEnvironmentNarrowing; OperationalValueNarrowing)
open import Typing.InterpreterSemanticTypingCore using
  (WorldTyping; ⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties using
  (runtime-narrowing-weaken)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing using (TypedValueNarrowing)
open import Narrowing.InterpreterTypedValueNarrowingProperties using
  (typed-value-narrowing-weaken)
import NuTermImprecision as NTI
import proof.InterpreterFramedValueNarrowingProof as Proof
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds
open Narrowing.InterpreterTermNarrowing.InterpreterValues

typed-value-type-transport :
  ∀ {W W′ A A′ B B′ V V′}
    {R : WorldRelation W W′} →
  A ≡ A′ →
  B ≡ B′ →
  TypedValueNarrowing A B R V V′ →
  TypedValueNarrowing A′ B′ R V V′
typed-value-type-transport refl refl typed =
  typed

framed-value-narrowing-weaken :
  ∀ {W W′ U U′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {A A′ : Ty} {V V′ : Value}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (R≤S : WorldExtension R S) →
  (U⊢ : WorldTyping U) →
  (U′⊢ : WorldTyping U′) →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p}
    (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime) V V′
framed-value-narrowing-weaken =
  Proof.framed-value-narrowing-weaken

framed-value-narrowing-future :
  ∀ {W W′ U U′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {A A′ : Ty} {V V′ : Value}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {runtimeS : RuntimeNarrowing S Φ Δᴸ Δᴿ ρ θ θ′} →
  WorldExtension R S →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtimeS V V′
framed-value-narrowing-future {runtimeS = runtimeS} R≤S value =
  reframed-value
    (typed-value-narrowing-weaken R≤S
      (left-world-typed runtimeS)
      (right-world-typed runtimeS)
      (Proof.framed-value-typed value))
    (framed-value-narrowing-weaken R≤S
      (left-world-typed runtimeS)
      (right-world-typed runtimeS)
      value)

framed-environment-narrowing-weaken :
  ∀ {W W′ U U′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {γ γ′ : Environment}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (R≤S : WorldExtension R S) →
  (U⊢ : WorldTyping U) →
  (U′⊢ : WorldTyping U′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  FramedEnvironmentNarrowing
    (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
    γᵀ γ γ′
framed-environment-narrowing-weaken =
  Proof.framed-environment-narrowing-weaken

framed-value-typed :
  ∀ {W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {A A′ : Ty} {V V′ : Value}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  TypedValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′
framed-value-typed =
  Proof.framed-value-typed

framed-value-operational :
  ∀ {W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {A A′ : Ty} {V V′ : Value}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′
framed-value-operational =
  Proof.framed-value-operational

framed-environment-operational :
  ∀ {W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {γ γ′ : Environment}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′
framed-environment-operational =
  Proof.framed-environment-operational

framed-value-erases :
  ∀ {W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {A A′ : Ty} {V V′ : Value}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  ValueNarrowing R V V′
framed-value-erases =
  Proof.framed-value-erases

framed-result-erases :
  ∀ {W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {A A′ : Ty} {V V′ : Value}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : WorldRelation W W′} →
  FramedValueResult ρ θ θ′ p R V V′ →
  ValueNarrowing R V V′
framed-result-erases =
  Proof.framed-result-erases

framed-environment-reframe :
  ∀ {W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {γ γ′ : Environment}
    {R : WorldRelation W W′}
    {runtime runtime′ :
      RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  FramedEnvironmentNarrowing runtime′ γᵀ γ γ′
framed-environment-reframe =
  Proof.framed-environment-reframe

operational-environment-frame :
  ∀ {W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
    {γ γ′ : Environment}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′
operational-environment-frame =
  Proof.operational-environment-frame
