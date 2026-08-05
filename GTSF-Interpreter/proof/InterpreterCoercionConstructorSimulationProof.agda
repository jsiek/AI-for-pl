module proof.InterpreterCoercionConstructorSimulationProof where

-- File Charter:
--   * Proves direct terminal simulation for coercions that return immediately.
--   * Covers paired and one-sided identity, proxy, tag, and generalization.
--   * Uses explicit interpreter equations and no reduction semantics.

open import Agda.Builtin.Equality using (refl)
open import Coercions renaming
  ( id to idᶜ
  ; _↦_ to _↦ᶜ_
  ; `∀ to ∀ᶜ
  ; _! to _!ᶜ
  ; gen to genᶜ
  )
open import Data.Product using (_,_; proj₁; proj₂)

open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; ⊑-src-wf; ⊑-tgt-wf)
open import Interpreter
open import Simulation.Coercion.InterpreterCoercionComputation
open import Narrowing.InterpreterCoercionNarrowing
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTagNarrowing
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterWorldNarrowing using (TypeEnvironmentScoped)
import Runtime.InterpreterTypeEnvironmentRealization as TER
open import Narrowing.InterpreterWorldNarrowingProperties
open import proof.InterpreterCoercionTyping using
  (ground?-complete; runtime-ground-from-typing; tagOf-complete)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)
open import Types

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module WorldProperties =
  WorldNarrowingProperties InterpreterTypeNarrowing

paired-id-coercion-simulation :
  ∀ {W W′ θ θ′ A A′ V V′}
    {R : WorldRelation W W′} →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (idᶜ A) V)
    (coerceValue W′ θ′ (idᶜ A′) V′)
paired-id-coercion-simulation V~V′ =
  simulation-pointwise
    coerce-id-computation coerce-id-computation
    (immediate-return-simulation V~V′)

paired-function-coercion-simulation :
  ∀ {W W′ θ θ′ p p′ q q′ V V′}
    {R : WorldRelation W W′} →
  PersistentSemanticCoercionNarrowing R θ θ′ p p′ →
  PersistentSemanticCoercionNarrowing R θ θ′ q q′ →
  TypeEnvironmentNarrowing R θ θ′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (p ↦ᶜ q) V)
    (coerceValue W′ θ′ (p′ ↦ᶜ q′) V′)
paired-function-coercion-simulation p~p′ q~q′ θ~θ′ V~V′ =
  simulation-pointwise
    coerce-function-computation coerce-function-computation
    (immediate-return-simulation
      (function-proxy⊑ p~p′ q~q′ θ~θ′ V~V′))

left-function-coercion-simulation :
  ∀ {W W′ θ p q V V′}
    {R : WorldRelation W W′} →
  PersistentLeftFunctionProxyBoundary R θ p q →
  TypeEnvironmentScoped W θ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (p ↦ᶜ q) V)
    (immediateReturn W′ V′)
left-function-coercion-simulation boundary θ-ok V~V′ =
  simulation-pointwise
    coerce-function-computation (λ n → refl)
    (immediate-return-simulation
      (left-function-proxy⊑ boundary θ-ok V~V′))

right-function-coercion-simulation :
  ∀ {W W′ θ′ p′ q′ V V′}
    {R : WorldRelation W W′} →
  PersistentRightFunctionProxyBoundary R θ′ p′ q′ →
  TypeEnvironmentScoped W′ θ′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (immediateReturn W V)
    (coerceValue W′ θ′ (p′ ↦ᶜ q′) V′)
right-function-coercion-simulation boundary θ′-ok V~V′ =
  simulation-pointwise
    (λ n → refl)
    coerce-function-computation
    (immediate-return-simulation
      (right-function-proxy⊑ boundary θ′-ok V~V′))

paired-forall-coercion-simulation :
  ∀ {W W′ θ θ′ c c′ V V′}
    {R : WorldRelation W W′} →
  PersistentSemanticCoercionNarrowing R θ θ′ c c′ →
  TypeEnvironmentNarrowing R θ θ′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (∀ᶜ c) V)
    (coerceValue W′ θ′ (∀ᶜ c′) V′)
paired-forall-coercion-simulation c~c′ θ~θ′ V~V′ =
  simulation-pointwise
    coerce-forall-computation coerce-forall-computation
    (immediate-return-simulation
      (forall-proxy⊑ c~c′ θ~θ′ V~V′))

left-forall-coercion-simulation :
  ∀ {W W′ θ c V V′}
    {R : WorldRelation W W′} →
  PersistentLeftForallProxyBoundary R θ c →
  TypeEnvironmentScoped W θ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (∀ᶜ c) V)
    (immediateReturn W′ V′)
left-forall-coercion-simulation boundary θ-ok V~V′ =
  simulation-pointwise
    coerce-forall-computation (λ n → refl)
    (immediate-return-simulation
      (left-forall-proxy⊑ boundary θ-ok V~V′))

right-forall-coercion-simulation :
  ∀ {W W′ θ′ c′ V V′}
    {R : WorldRelation W W′} →
  PersistentRightForallProxyBoundary R θ′ c′ →
  TypeEnvironmentScoped W′ θ′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (immediateReturn W V)
    (coerceValue W′ θ′ (∀ᶜ c′) V′)
right-forall-coercion-simulation boundary θ′-ok V~V′ =
  simulation-pointwise
    (λ n → refl)
    coerce-forall-computation
    (immediate-return-simulation
      (right-forall-proxy⊑ boundary θ′-ok V~V′))

paired-tag-coercion-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ G H V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  RuntimeTypeEnvironment θ →
  (G~H : Φ ∣ Δᴸ ⊢ G ⊑ H ⊣ Δᴿ) →
  (gG : Ground G) →
  (gH : Ground H) →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (G !ᶜ) V)
    (coerceValue W′ θ′ (H !ᶜ) V′)
paired-tag-coercion-simulation runtime runtime-env G~H gG gH V~V′
    with ground?-complete
           (runtime-ground-from-typing runtime-env
             (left-runtime-context runtime) (⊑-src-wf G~H) gG)
       | ground?-complete
           (runtime-ground-from-typing
             (right-runtime-environment runtime)
             (right-runtime-context runtime) (⊑-tgt-wf G~H) gH)
paired-tag-coercion-simulation runtime runtime-env G~H gG gH V~V′
    | gG′ , ground-eq | gH′ , ground-eq′
    with tagOf-complete (left-runtime-context runtime)
           (⊑-src-wf G~H) (runtime-ground-syntax gG′)
       | tagOf-complete (right-runtime-context runtime)
           (⊑-tgt-wf G~H) (runtime-ground-syntax gH′)
paired-tag-coercion-simulation runtime runtime-env G~H gG gH V~V′
    | gG′ , ground-eq | gH′ , ground-eq′
    | tag , tag-eq | tag′ , tag-eq′ =
  simulation-pointwise
    (coerce-tag-computation ground-eq tag-eq)
    (coerce-tag-computation ground-eq′ tag-eq′)
    (immediate-return-simulation
      (tagged⊑
        (ground-narrowing (type-narrowing G~H))
        (TER.environments-narrow
          (type-environments-realized runtime))
        V~V′))

left-tag-coercion-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ G V V′}
    {R : WorldRelation W W′}
    {gG : Ground G} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  RuntimeTypeEnvironment θ →
  (G~★ : Φ ∣ Δᴸ ⊢ G ⊑ ★ ⊣ Δᴿ) →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (G !ᶜ) V)
    (immediateReturn W′ V′)
left-tag-coercion-simulation {gG = gG}
    runtime runtime-env G~★ V~V′
    with ground?-complete
      (runtime-ground-from-typing runtime-env
        (left-runtime-context runtime) (⊑-src-wf G~★) gG)
left-tag-coercion-simulation {gG = gG}
    runtime runtime-env G~★ V~V′
    | gG′ , ground-eq
    with tagOf-complete (left-runtime-context runtime)
      (⊑-src-wf G~★) (runtime-ground-syntax gG′)
left-tag-coercion-simulation {gG = gG}
    runtime runtime-env G~★ V~V′
    | gG′ , ground-eq | tag , tag-eq =
  simulation-pointwise
    (coerce-tag-computation ground-eq tag-eq)
    (λ n → refl)
    (immediate-return-simulation
      (left-tagged⊑ (type-narrowing G~★)
        (WorldProperties.type-environment-left-scoped
          (TER.environments-narrow
            (type-environments-realized runtime)))
        V~V′))

right-tag-coercion-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ H V V′}
    {R : WorldRelation W W′}
    {gH : Ground H} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (★~H : Φ ∣ Δᴸ ⊢ ★ ⊑ H ⊣ Δᴿ) →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (immediateReturn W V)
    (coerceValue W′ θ′ (H !ᶜ) V′)
right-tag-coercion-simulation {gH = gH} runtime ★~H V~V′
    with ground?-complete
      (runtime-ground-from-typing
        (right-runtime-environment runtime)
        (right-runtime-context runtime) (⊑-tgt-wf ★~H) gH)
right-tag-coercion-simulation {gH = gH} runtime ★~H V~V′
    | gH′ , ground-eq
    with tagOf-complete (right-runtime-context runtime)
      (⊑-tgt-wf ★~H) (runtime-ground-syntax gH′)
right-tag-coercion-simulation {gH = gH} runtime ★~H V~V′
    | gH′ , ground-eq | tag′ , tag-eq′ =
  simulation-pointwise
    (λ n → refl)
    (coerce-tag-computation ground-eq tag-eq′)
    (immediate-return-simulation
      (right-tagged⊑ (type-narrowing ★~H)
        (WorldProperties.type-environment-right-scoped
          (TER.environments-narrow
            (type-environments-realized runtime)))
        V~V′))

paired-generalization-coercion-simulation :
  ∀ {W W′ θ θ′ A A′ c c′ V V′}
    {R : WorldRelation W W′} →
  InterpreterTypeNarrowing A A′ →
  PersistentSemanticCoercionNarrowing R θ θ′ c c′ →
  TypeEnvironmentNarrowing R θ θ′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (genᶜ A c) V)
    (coerceValue W′ θ′ (genᶜ A′ c′) V′)
paired-generalization-coercion-simulation
    A~A′ c~c′ θ~θ′ V~V′ =
  simulation-pointwise
    coerce-generalization-computation
    coerce-generalization-computation
    (immediate-return-simulation
      (generalized⊑ A~A′ c~c′ θ~θ′ V~V′))

left-generalization-coercion-simulation :
  ∀ {W W′ θ A c V V′}
    {R : WorldRelation W W′} →
  PersistentLeftGeneralizationBoundary R θ A c →
  TypeEnvironmentScoped W θ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (genᶜ A c) V)
    (immediateReturn W′ V′)
left-generalization-coercion-simulation boundary θ-ok V~V′ =
  simulation-pointwise
    coerce-generalization-computation
    (λ n → refl)
    (immediate-return-simulation
      (left-generalized⊑ boundary θ-ok V~V′))

right-generalization-coercion-simulation :
  ∀ {W W′ θ′ A′ c′ V V′}
    {R : WorldRelation W W′} →
  PersistentRightGeneralizationBoundary R θ′ A′ c′ →
  TypeEnvironmentScoped W′ θ′ →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (immediateReturn W V)
    (coerceValue W′ θ′ (genᶜ A′ c′) V′)
right-generalization-coercion-simulation boundary θ′-ok V~V′ =
  simulation-pointwise
    (λ n → refl)
    coerce-generalization-computation
    (immediate-return-simulation
      (right-generalized⊑ boundary θ′-ok V~V′))
