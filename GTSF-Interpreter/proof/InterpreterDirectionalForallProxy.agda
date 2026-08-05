module proof.InterpreterDirectionalForallProxy where

-- File Charter:
--   * Derives directional instantiation observations for paired and
--     one-sided forall proxies.
--   * Uses a zero index at the endpoint irrelevant to the observation.
--   * Contains no interpreter recursion, reduction, or quotient argument.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedForallProxy
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterDirectionalSimulation using
  (backward-at-left-zero; forward-at-right-zero)

open ITN.RelatedWorlds

directional-paired-forall-proxy-forward :
  ∀ {W W′ α α′ θ θ′ c c′ V V′ index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  ForwardReturnSimulation head-result R
    (instantiateValue W α V)
    (instantiateValue W′ α′ V′) index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    ForwardReturnSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  ForwardReturnSimulation result R
    (instantiateValue W α (forall-proxy c θ V))
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
    (suc index)
directional-paired-forall-proxy-forward
    {index = index} head tail =
  forward-return
    (indexed-paired-forall-proxy-instantiation
      {left-index = index} {right-index = zero}
      (forward-at-right-zero refl head)
      (λ R≤S U~U′ →
        forward-at-right-zero refl (tail R≤S U~U′)))

paired-forall-proxy-backward-bundle :
  ∀ {W W′ α α′ θ θ′ c c′ V V′ index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation head-result R
    (instantiateValue W α V)
    (instantiateValue W′ α′ V′) index →
  TargetBlameSimulation R
    (instantiateValue W α V)
    (instantiateValue W′ α′ V′) index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    BackwardReturnSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    TargetBlameSimulation S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  IndexedTerminalSimulation result R
    (instantiateValue W α (forall-proxy c θ V))
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
    (suc zero) (suc index)
paired-forall-proxy-backward-bundle
    {index = index} head-backward head-blame
    tail-backward tail-blame =
  indexed-paired-forall-proxy-instantiation
    {left-index = zero} {right-index = index}
    (backward-at-left-zero refl head-backward head-blame)
    (λ R≤S U~U′ →
      backward-at-left-zero refl
        (tail-backward R≤S U~U′)
        (tail-blame R≤S U~U′))

directional-paired-forall-proxy-backward :
  ∀ {W W′ α α′ θ θ′ c c′ V V′ index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation head-result R
    (instantiateValue W α V)
    (instantiateValue W′ α′ V′) index →
  TargetBlameSimulation R
    (instantiateValue W α V)
    (instantiateValue W′ α′ V′) index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    BackwardReturnSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    TargetBlameSimulation S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  BackwardReturnSimulation result R
    (instantiateValue W α (forall-proxy c θ V))
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
    (suc index)
directional-paired-forall-proxy-backward
    {W} {W′} {α} {α′} {θ} {θ′} {c} {c′}
    {V} {V′} {index} {head-result} {result} {R}
    head-backward head-blame tail-backward tail-blame =
  backward-return
    (paired-forall-proxy-backward-bundle
      {W = W} {W′ = W′} {α = α} {α′ = α′}
      {θ = θ} {θ′ = θ′} {c = c} {c′ = c′}
      {V = V} {V′ = V′} {index = index}
      {head-result = head-result} {result = result} {R = R}
      head-backward head-blame tail-backward tail-blame)

directional-paired-forall-proxy-target-blame :
  ∀ {W W′ α α′ θ θ′ c c′ V V′ index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation head-result R
    (instantiateValue W α V)
    (instantiateValue W′ α′ V′) index →
  TargetBlameSimulation R
    (instantiateValue W α V)
    (instantiateValue W′ α′ V′) index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    BackwardReturnSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    TargetBlameSimulation S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  TargetBlameSimulation R
    (instantiateValue W α (forall-proxy c θ V))
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
    (suc index)
directional-paired-forall-proxy-target-blame
    {W} {W′} {α} {α′} {θ} {θ′} {c} {c′}
    {V} {V′} {index} {head-result} {result} {R}
    head-backward head-blame tail-backward tail-blame =
  target-blame-reflects
    (paired-forall-proxy-backward-bundle
      {W = W} {W′ = W′} {α = α} {α′ = α′}
      {θ = θ} {θ′ = θ′} {c = c} {c′ = c′}
      {V = V} {V′ = V′} {index = index}
      {head-result = head-result} {result = result} {R = R}
      head-backward head-blame tail-backward tail-blame)

directional-left-forall-proxy-forward :
  ∀ {W W′ α θ c V V′ index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  ForwardReturnSimulation head-result R
    (instantiateValue W α V) (immediateReturn W′ V′) index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    ForwardReturnSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (immediateReturn Z′ U′) index) →
  ForwardReturnSimulation result R
    (instantiateValue W α (forall-proxy c θ V))
    (immediateReturn W′ V′) (suc index)
directional-left-forall-proxy-forward
    {index = index} head tail =
  forward-return
    (indexed-left-forall-proxy-instantiation
      {left-index = index} {right-index = zero}
      (forward-at-right-zero refl head)
      (λ R≤S U~U′ →
        forward-at-right-zero refl (tail R≤S U~U′)))

left-forall-proxy-backward-bundle :
  ∀ {W W′ α θ c V V′ index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation head-result R
    (instantiateValue W α V) (immediateReturn W′ V′) index →
  TargetBlameSimulation R
    (instantiateValue W α V) (immediateReturn W′ V′) index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    BackwardReturnSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (immediateReturn Z′ U′) index) →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    TargetBlameSimulation S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (immediateReturn Z′ U′) index) →
  IndexedTerminalSimulation result R
    (instantiateValue W α (forall-proxy c θ V))
    (immediateReturn W′ V′)
    (suc zero) index
left-forall-proxy-backward-bundle
    {index = index} head-backward head-blame
    tail-backward tail-blame =
  indexed-left-forall-proxy-instantiation
    {left-index = zero} {right-index = index}
    (backward-at-left-zero refl head-backward head-blame)
    (λ R≤S U~U′ →
      backward-at-left-zero refl
        (tail-backward R≤S U~U′)
        (tail-blame R≤S U~U′))

directional-left-forall-proxy-backward :
  ∀ {W W′ α θ c V V′ index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation head-result R
    (instantiateValue W α V) (immediateReturn W′ V′) index →
  TargetBlameSimulation R
    (instantiateValue W α V) (immediateReturn W′ V′) index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    BackwardReturnSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (immediateReturn Z′ U′) index) →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    TargetBlameSimulation S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (immediateReturn Z′ U′) index) →
  BackwardReturnSimulation result R
    (instantiateValue W α (forall-proxy c θ V))
    (immediateReturn W′ V′) index
directional-left-forall-proxy-backward
    head-backward head-blame tail-backward tail-blame =
  backward-return
    (left-forall-proxy-backward-bundle
      head-backward head-blame tail-backward tail-blame)

directional-left-forall-proxy-target-blame :
  ∀ {W W′ α θ c V V′ index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation head-result R
    (instantiateValue W α V) (immediateReturn W′ V′) index →
  TargetBlameSimulation R
    (instantiateValue W α V) (immediateReturn W′ V′) index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    BackwardReturnSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (immediateReturn Z′ U′) index) →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    TargetBlameSimulation S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (immediateReturn Z′ U′) index) →
  TargetBlameSimulation R
    (instantiateValue W α (forall-proxy c θ V))
    (immediateReturn W′ V′) index
directional-left-forall-proxy-target-blame
    head-backward head-blame tail-backward tail-blame =
  target-blame-reflects
    (left-forall-proxy-backward-bundle
      head-backward head-blame tail-backward tail-blame)

right-forall-proxy-forward-bundle :
  ∀ {W W′ α′ θ′ c′ V V′ index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  ForwardReturnSimulation head-result R
    (immediateReturn W V)
    (instantiateValue W′ α′ V′) index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    ForwardReturnSimulation result S
      (immediateReturn Z U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  IndexedTerminalSimulation result R
    (immediateReturn W V)
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
    index (suc zero)
right-forall-proxy-forward-bundle
    {index = index} head tail =
  indexed-right-forall-proxy-instantiation
    {left-index = index} {right-index = zero}
    (forward-at-right-zero refl head)
    (λ R≤S U~U′ →
      forward-at-right-zero refl (tail R≤S U~U′))

directional-right-forall-proxy-forward :
  ∀ {W W′ α′ θ′ c′ V V′ index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  ForwardReturnSimulation head-result R
    (immediateReturn W V)
    (instantiateValue W′ α′ V′) index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    ForwardReturnSimulation result S
      (immediateReturn Z U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  ForwardReturnSimulation result R
    (immediateReturn W V)
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
    index
directional-right-forall-proxy-forward head tail =
  forward-return
    (right-forall-proxy-forward-bundle head tail)

directional-right-forall-proxy-backward :
  ∀ {W W′ α′ θ′ c′ V V′ index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation head-result R
    (immediateReturn W V)
    (instantiateValue W′ α′ V′) index →
  TargetBlameSimulation R
    (immediateReturn W V)
    (instantiateValue W′ α′ V′) index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    BackwardReturnSimulation result S
      (immediateReturn Z U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    TargetBlameSimulation S
      (immediateReturn Z U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  BackwardReturnSimulation result R
    (immediateReturn W V)
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
    (suc index)
directional-right-forall-proxy-backward
    {index = index} head-backward head-blame
    tail-backward tail-blame =
  backward-return
    (indexed-right-forall-proxy-instantiation
      {left-index = zero} {right-index = index}
      (backward-at-left-zero refl head-backward head-blame)
      (λ R≤S U~U′ →
        backward-at-left-zero refl
          (tail-backward R≤S U~U′)
          (tail-blame R≤S U~U′)))

directional-right-forall-proxy-target-blame :
  ∀ {W W′ α′ θ′ c′ V V′ index}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation head-result R
    (immediateReturn W V)
    (instantiateValue W′ α′ V′) index →
  TargetBlameSimulation R
    (immediateReturn W V)
    (instantiateValue W′ α′ V′) index →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    BackwardReturnSimulation result S
      (immediateReturn Z U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  (∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    head-result S U U′ →
    TargetBlameSimulation S
      (immediateReturn Z U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)
      index) →
  TargetBlameSimulation R
    (immediateReturn W V)
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
    (suc index)
directional-right-forall-proxy-target-blame
    {index = index} head-backward head-blame
    tail-backward tail-blame =
  target-blame-reflects
    (indexed-right-forall-proxy-instantiation
      {left-index = zero} {right-index = index}
      (backward-at-left-zero refl head-backward head-blame)
      (λ R≤S U~U′ →
        backward-at-left-zero refl
          (tail-backward R≤S U~U′)
          (tail-blame R≤S U~U′)))
