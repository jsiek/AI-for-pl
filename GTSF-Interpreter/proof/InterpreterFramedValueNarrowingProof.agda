module proof.InterpreterFramedValueNarrowingProof where

-- File Charter:
--   * Proves weakening and public erasure for runtime-framed values.
--   * Recurses exhaustively over exact value and environment origins.
--   * Uses only world extension and structural narrowing metatheory.

open import Narrowing.InterpreterFramedValueNarrowing
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter using
  (Environment; TypeEnvironment; Value; World)
open import Narrowing.InterpreterQuotientValueNarrowing using
  (quotient-value-frame-weaken)
open import Narrowing.InterpreterOperationalValueNarrowing using
  ( OperationalEnvironmentNarrowing
  ; OperationalValueNarrowing
  ; []⊑[]ᵒ
  ; _∷⊑∷ᵒ_
  ; operational-typed
  )
open import Narrowing.InterpreterOperationalValueNarrowingProperties using
  (operational-value-narrowing-weaken)
open import Typing.InterpreterSemanticTypingCore using
  (WorldTyping; ⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext using
  (RuntimeNarrowing)
open import Simulation.Core.InterpreterSimulationContextProperties using
  (environment-realization-weaken; runtime-narrowing-weaken)
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing using
  (TypedValueNarrowing; values-narrow)
open import Narrowing.InterpreterTypedValueNarrowingProperties using
  (typed-value-narrowing-weaken)
import Narrowing.InterpreterCoercionNarrowing as ICN
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties
import NuTermImprecision as NTI
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds
open Narrowing.InterpreterTermNarrowing.InterpreterValues

module FramedWorldProperties =
  WorldProperties.WorldNarrowingProperties
    ICN.InterpreterTypeNarrowing

mutual

  framed-value-narrowing-weaken :
    ∀ {W W′ U U′}
      {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ θ′ : TypeEnvironment}
      {A A′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {V V′ : Value}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′}
      {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
    (R≤S : WorldExtension R S) →
    (U⊢ : WorldTyping U) →
    (U′⊢ : WorldTyping U′) →
    FramedValueNarrowing
      {A = A} {A′ = A′} {p = p} runtime V V′ →
    FramedValueNarrowing
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime) V V′
  framed-value-narrowing-weaken R≤S U⊢ U′⊢
      (framed-value typed operational origin) =
    framed-value
      (typed-value-narrowing-weaken R≤S U⊢ U′⊢ typed)
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ operational)
      (framed-value-origin-weaken R≤S U⊢ U′⊢ origin)
  framed-value-narrowing-weaken R≤S U⊢ U′⊢
      (reframed-value typed value) =
    reframed-value
      (typed-value-narrowing-weaken R≤S U⊢ U′⊢ typed)
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-narrowing-weaken R≤S U⊢ U′⊢
      (reindexed-value typed value) =
    reindexed-value
      (typed-value-narrowing-weaken R≤S U⊢ U′⊢ typed)
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-narrowing-weaken R≤S U⊢ U′⊢
      (operationally-framed-value value) =
    operationally-framed-value
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-narrowing-weaken R≤S U⊢ U′⊢
      (compiler-replanned-value typed operational value) =
    compiler-replanned-value
      (typed-value-narrowing-weaken R≤S U⊢ U′⊢ typed)
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ operational)
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-narrowing-weaken R≤S U⊢ U′⊢
      (left-name-instantiated-value
        typed operational Q≤P α-ok result-eq value) =
    left-name-instantiated-value
      (typed-value-narrowing-weaken R≤S U⊢ U′⊢ typed)
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ operational)
      (FramedWorldProperties.world-extension-trans Q≤P R≤S)
      (FramedWorldProperties.allocated-left-weaken R≤S α-ok)
      result-eq value
  framed-value-narrowing-weaken R≤S U⊢ U′⊢
      (paired-lifted-value
        unique left-eq right-eq P≤R typed operational value) =
    paired-lifted-value unique left-eq right-eq
      (FramedWorldProperties.world-extension-trans P≤R R≤S)
      (typed-value-narrowing-weaken R≤S U⊢ U′⊢ typed)
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ operational)
      value
  framed-value-narrowing-weaken R≤S U⊢ U′⊢
      (paired-unlifted-value unique typed operational value) =
    paired-unlifted-value unique
      (typed-value-narrowing-weaken R≤S U⊢ U′⊢ typed)
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ operational)
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-narrowing-weaken R≤S U⊢ U′⊢
      (left-lifted-value
        unique left-eq P≤R typed operational value) =
    left-lifted-value unique left-eq
      (FramedWorldProperties.world-extension-trans P≤R R≤S)
      (typed-value-narrowing-weaken R≤S U⊢ U′⊢ typed)
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ operational)
      value
  framed-value-narrowing-weaken R≤S U⊢ U′⊢
      (left-unlifted-value unique typed operational value) =
    left-unlifted-value unique
      (typed-value-narrowing-weaken R≤S U⊢ U′⊢ typed)
      (operational-value-narrowing-weaken R≤S U⊢ U′⊢ operational)
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)

  framed-value-origin-weaken :
    ∀ {W W′ U U′}
      {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ θ′ : TypeEnvironment}
      {A A′ : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {V V′ : Value}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′}
      {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
    (R≤S : WorldExtension R S) →
    (U⊢ : WorldTyping U) →
    (U′⊢ : WorldTyping U′) →
    FramedValueOrigin runtime p V V′ →
    FramedValueOrigin
      (runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime)
      p V V′
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (closure-originᶠ environment values terms) =
    closure-originᶠ
      (environment-realization-weaken R≤S U⊢ U′⊢ environment)
      (framed-environment-narrowing-weaken R≤S U⊢ U′⊢ values)
      (open-interpreter-narrowing-world-weaken R≤S terms)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      constant-originᶠ =
    constant-originᶠ
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (paired-tag-originᶠ action value) =
    paired-tag-originᶠ action
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (left-tag-originᶠ action value) =
    left-tag-originᶠ action
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (right-tag-originᶠ action value) =
    right-tag-originᶠ action
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (paired-seal-originᶠ action value) =
    paired-seal-originᶠ action
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (left-seal-originᶠ action value) =
    left-seal-originᶠ action
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (paired-function-originᶠ action domain codomain value) =
    paired-function-originᶠ action domain codomain
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (left-function-originᶠ action domain codomain value) =
    left-function-originᶠ action domain codomain
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (right-function-originᶠ action domain codomain value) =
    right-function-originᶠ action domain codomain
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (paired-type-abstraction-originᶠ lift instantiate) =
    paired-type-abstraction-originᶠ lift
      (λ S≤T C~C′ σ~σ′ allocated →
        instantiate
          (FramedWorldProperties.world-extension-trans R≤S S≤T)
          C~C′ σ~σ′ allocated)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (left-type-abstraction-originᶠ lift instantiate) =
    left-type-abstraction-originᶠ lift
      (λ S≤T σ-ok allocated →
        instantiate
          (FramedWorldProperties.world-extension-trans R≤S S≤T)
          σ-ok allocated)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (paired-forall-originᶠ action lift component value) =
    paired-forall-originᶠ action lift component
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (left-forall-originᶠ action lift component value) =
    left-forall-originᶠ action lift component
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (right-forall-originᶠ action lift component value) =
    right-forall-originᶠ action lift component
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (paired-generalized-originᶠ action value) =
    paired-generalized-originᶠ action
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (left-generalized-originᶠ action value) =
    left-generalized-originᶠ action
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (right-generalized-originᶠ action value) =
    right-generalized-originᶠ action
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (operational-quotient-originᶠ
        D⊑E alignment down up frame value) =
    operational-quotient-originᶠ
      D⊑E alignment down up
      (quotient-value-frame-weaken R≤S frame)
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)
  framed-value-origin-weaken R≤S U⊢ U′⊢
      (quotient-originᶠ base terms frame value) =
    quotient-originᶠ
      (open-interpreter-narrowing-world-weaken R≤S base)
      (open-interpreter-narrowing-world-weaken R≤S terms)
      (quotient-value-frame-weaken R≤S frame)
      (framed-value-narrowing-weaken R≤S U⊢ U′⊢ value)

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
  framed-environment-narrowing-weaken R≤S U⊢ U′⊢
      []⊑[]ᶠ =
    []⊑[]ᶠ
  framed-environment-narrowing-weaken R≤S U⊢ U′⊢
      (value ∷⊑∷ᶠ environment) =
    framed-value-narrowing-weaken R≤S U⊢ U′⊢ value
      ∷⊑∷ᶠ
    framed-environment-narrowing-weaken R≤S U⊢ U′⊢ environment

framed-value-typed :
  ∀ {W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {V V′ : Value}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  TypedValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′
framed-value-typed (framed-value typed operational origin) =
  typed
framed-value-typed (reframed-value typed value) =
  typed
framed-value-typed (reindexed-value typed value) =
  typed
framed-value-typed (operationally-framed-value value) =
  operational-typed value
framed-value-typed
    (compiler-replanned-value typed operational value) =
  typed
framed-value-typed
    (left-name-instantiated-value
      typed operational R≤S α-ok result-eq value) =
  typed
framed-value-typed
    (paired-lifted-value
      unique left-eq right-eq R≤S typed operational value) =
  typed
framed-value-typed
    (paired-unlifted-value unique typed operational value) =
  typed
framed-value-typed
    (left-lifted-value unique left-eq R≤S typed operational value) =
  typed
framed-value-typed
    (left-unlifted-value unique typed operational value) =
  typed

framed-value-operational :
  ∀ {W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {V V′ : Value}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′
framed-value-operational
    (framed-value typed operational origin) =
  operational
framed-value-operational (reframed-value typed value) =
  framed-value-operational value
framed-value-operational (reindexed-value typed value) =
  framed-value-operational value
framed-value-operational (operationally-framed-value operational) =
  operational
framed-value-operational
    (compiler-replanned-value typed operational value) =
  operational
framed-value-operational
    (left-name-instantiated-value
      typed operational R≤S α-ok result-eq value) =
  operational
framed-value-operational
    (paired-lifted-value
      unique left-eq right-eq R≤S typed operational value) =
  operational
framed-value-operational
    (paired-unlifted-value unique typed operational value) =
  operational
framed-value-operational
    (left-lifted-value unique left-eq R≤S typed operational value) =
  operational
framed-value-operational
    (left-unlifted-value unique typed operational value) =
  operational

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
framed-environment-operational []⊑[]ᶠ =
  []⊑[]ᵒ
framed-environment-operational (value ∷⊑∷ᶠ environment) =
  framed-value-operational value
    ∷⊑∷ᵒ
  framed-environment-operational environment

framed-value-erases :
  ∀ {W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {V V′ : Value}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedValueNarrowing
    {A = A} {A′ = A′} {p = p} runtime V V′ →
  ValueNarrowing R V V′
framed-value-erases value =
  values-narrow (framed-value-typed value)

framed-result-erases :
  ∀ {W W′}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {V V′ : Value}
    {R : WorldRelation W W′} →
  FramedValueResult ρ θ θ′ p R V V′ →
  ValueNarrowing R V V′
framed-result-erases (framed-result runtime value) =
  framed-value-erases value

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
framed-environment-reframe []⊑[]ᶠ =
  []⊑[]ᶠ
framed-environment-reframe (value ∷⊑∷ᶠ environment) =
  reframed-value (framed-value-typed value) value
    ∷⊑∷ᶠ
  framed-environment-reframe environment

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
operational-environment-frame runtime []⊑[]ᵒ =
  []⊑[]ᶠ
operational-environment-frame runtime (value ∷⊑∷ᵒ environment) =
  operationally-framed-value value
    ∷⊑∷ᶠ
  operational-environment-frame runtime environment
