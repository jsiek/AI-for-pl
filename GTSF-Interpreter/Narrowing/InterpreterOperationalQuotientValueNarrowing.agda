module Narrowing.InterpreterOperationalQuotientValueNarrowing where

-- File Charter:
--   * Defines the intermediate relation produced by active quotient downcasts.
--   * Records the retained aligned route, exact runtime frame, input relation,
--     returned-world extension, and direct downcast return equations.
--   * Allows downcasts such as `inst` to allocate on either endpoint.
--   * Does not assume that either downcast is inert or add a runtime value.
--   * Contains no small-step reduction, catch-up result, or DGG theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (suc)

open import Coercions using (Coercion; Inert)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Runtime.InterpreterClosedValueFrame
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using
  (ValueResultRelation)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
open import proof.EndpointCanonicalMLBSimpleQuotient using
  ( EndpointRepresentativeAlignment
  ; endpoint-representatives-quotient
  )
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

data OperationalQuotientValueNarrowing
    {W W′ : World}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {C C′ D D′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′)
    (d d′ : Coercion)
    {X Y E : Ty}
    (D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ)
    (alignment :
      EndpointRepresentativeAlignment Δᴿ X Y E D′)
    (down :
      OperationalDownCoercionNarrowing
        Φ Δᴸ Δᴿ ρ d d′ pC
        (endpoint-representatives-quotient D⊑E alignment)) :
    ValueResultRelation where

  quotient-down-return :
    ∀ {U U′ : World}
      {S : WorldRelation U U′}
      {V V′ L L′ : Value}
      {left-index right-index : StepIndex} →
    WorldExtension R S →
    (returned-runtime :
      RuntimeNarrowing S Φ Δᴸ Δᴿ ρ θ θ′) →
    FramedValueNarrowing
      {A = C} {A′ = C′} {p = pC} runtime V V′ →
    coerceValue W θ d V left-index ≡ returned U L →
    coerceValue W′ θ′ d′ V′ right-index ≡ returned U′ L′ →
    OperationalQuotientValueNarrowing
      runtime d d′ D⊑E alignment down S L L′

  quotient-down-inert-return :
    ∀ {V V′ L L′ : Value}
      {left-inert : Inert d}
      {right-inert : Inert d′} →
    FramedValueNarrowing
      {A = C} {A′ = C′} {p = pC} runtime V V′ →
    ClosedValueFrame θ V left-inert L →
    ClosedValueFrame θ′ V′ right-inert L′ →
    (∀ n → coerceValue W θ d V (suc n)
      ≡ returned W L) →
    (∀ n → coerceValue W′ θ′ d′ V′ (suc n)
      ≡ returned W′ L′) →
    OperationalQuotientValueNarrowing
      runtime d d′ D⊑E alignment down R L L′

quotient-down-extension :
  ∀ {W W′ : World}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {C C′ D D′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {d d′ : Coercion}
    {X Y E : Ty}
    {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    {alignment : EndpointRepresentativeAlignment Δᴿ X Y E D′}
    {down :
      OperationalDownCoercionNarrowing
        Φ Δᴸ Δᴿ ρ d d′ pC
        (endpoint-representatives-quotient D⊑E alignment)}
    {U U′ : World}
    {S : WorldRelation U U′}
    {L L′ : Value}
    {runtime :
      RuntimeNarrowing
        {W = W} {W′ = W′} R Φ Δᴸ Δᴿ ρ θ θ′} →
  OperationalQuotientValueNarrowing
    {C = C} {C′ = C′} {D = D} {D′ = D′} {pC = pC}
    runtime d d′ {X = X} {Y = Y} {E = E}
    D⊑E alignment down S L L′ →
  WorldExtension R S
quotient-down-extension
    (quotient-down-return R≤S returned-runtime value left-eq right-eq) =
  R≤S
quotient-down-extension
    (quotient-down-inert-return
      value left-frame right-frame left-eq right-eq) =
  extension-refl

quotient-down-runtime :
  ∀ {W W′ : World}
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
    {θ θ′ : TypeEnvironment}
    {C C′ D D′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {R : WorldRelation W W′}
    {d d′ : Coercion}
    {X Y E : Ty}
    {D⊑E : Φ ∣ Δᴸ ⊢ D ⊑ E ⊣ Δᴿ}
    {alignment : EndpointRepresentativeAlignment Δᴿ X Y E D′}
    {down :
      OperationalDownCoercionNarrowing
        Φ Δᴸ Δᴿ ρ d d′ pC
        (endpoint-representatives-quotient D⊑E alignment)}
    {U U′ : World}
    {S : WorldRelation U U′}
    {L L′ : Value}
    {runtime :
      RuntimeNarrowing
        {W = W} {W′ = W′} R Φ Δᴸ Δᴿ ρ θ θ′} →
  OperationalQuotientValueNarrowing
    {C = C} {C′ = C′} {D = D} {D′ = D′} {pC = pC}
    runtime d d′ {X = X} {Y = Y} {E = E}
    D⊑E alignment down S L L′ →
  RuntimeNarrowing S Φ Δᴸ Δᴿ ρ θ θ′
quotient-down-runtime
    (quotient-down-return R≤S returned-runtime value left-eq right-eq) =
  returned-runtime
quotient-down-runtime {runtime = runtime}
    (quotient-down-inert-return
      value left-frame right-frame left-eq right-eq) =
  runtime
