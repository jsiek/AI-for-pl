module proof.InterpreterDirectionalGeneralizedValue where

-- File Charter:
--   * Derives directional observations for paired and one-sided generalized
--     value instantiation.
--   * Reuses the indexed constructor guard at a zero-index endpoint.
--   * Contains no interpreter recursion, reduction, or quotient argument.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedGeneralizedValue
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterDirectionalSimulation using
  (backward-at-left-zero; forward-at-right-zero)

open ITN.RelatedWorlds

directional-paired-generalized-forward :
  ∀ {W W′ α α′ A A′ c c′ θ θ′ V V′ index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  ForwardReturnSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    index →
  ForwardReturnSimulation result R
    (instantiateValue W α (generalized A c θ V))
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
    (suc index)
directional-paired-generalized-forward
    {W} {W′} {α} {α′} {A} {A′} {c} {c′}
    {θ} {θ′} {V} {V′} {index} {result} {R} coercion =
  forward-return
    (indexed-paired-generalized-instantiation
      {W = W} {W′ = W′} {α = α} {α′ = α′}
      {A = A} {A′ = A′} {c = c} {c′ = c′}
      {θ = θ} {θ′ = θ′} {V = V} {V′ = V′}
      {left-index = index} {right-index = zero}
      {result = result} {R = R}
      (forward-at-right-zero refl coercion))

paired-generalized-backward-bundle :
  ∀ {W W′ α α′ A A′ c c′ θ θ′ V V′ index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    index →
  TargetBlameSimulation R
    (coerceValue W (seal-name α ∷ θ) c V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    index →
  IndexedTerminalSimulation result R
    (instantiateValue W α (generalized A c θ V))
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
    (suc zero) (suc index)
paired-generalized-backward-bundle
    {index = index} backward blame =
  indexed-paired-generalized-instantiation
    {left-index = zero} {right-index = index}
    (backward-at-left-zero refl backward blame)

directional-paired-generalized-backward :
  ∀ {W W′ α α′ A A′ c c′ θ θ′ V V′ index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    index →
  TargetBlameSimulation R
    (coerceValue W (seal-name α ∷ θ) c V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    index →
  BackwardReturnSimulation result R
    (instantiateValue W α (generalized A c θ V))
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
    (suc index)
directional-paired-generalized-backward
    {W} {W′} {α} {α′} {A} {A′} {c} {c′}
    {θ} {θ′} {V} {V′} {index} {result} {R}
    backward blame =
  backward-return
    (paired-generalized-backward-bundle
      {W = W} {W′ = W′} {α = α} {α′ = α′}
      {A = A} {A′ = A′} {c = c} {c′ = c′}
      {θ = θ} {θ′ = θ′} {V = V} {V′ = V′}
      {index = index} {result = result} {R = R}
      backward blame)

directional-paired-generalized-target-blame :
  ∀ {W W′ α α′ A A′ c c′ θ θ′ V V′ index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    index →
  TargetBlameSimulation R
    (coerceValue W (seal-name α ∷ θ) c V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    index →
  TargetBlameSimulation R
    (instantiateValue W α (generalized A c θ V))
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
    (suc index)
directional-paired-generalized-target-blame
    {W} {W′} {α} {α′} {A} {A′} {c} {c′}
    {θ} {θ′} {V} {V′} {index} {result} {R}
    backward blame =
  target-blame-reflects
    (paired-generalized-backward-bundle
      {W = W} {W′ = W′} {α = α} {α′ = α′}
      {A = A} {A′ = A′} {c = c} {c′ = c′}
      {θ = θ} {θ′ = θ′} {V = V} {V′ = V′}
      {index = index} {result = result} {R = R}
      backward blame)

directional-left-generalized-forward :
  ∀ {W W′ α A c θ V V′ index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  ForwardReturnSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (immediateReturn W′ V′) index →
  ForwardReturnSimulation result R
    (instantiateValue W α (generalized A c θ V))
    (immediateReturn W′ V′) (suc index)
directional-left-generalized-forward
    {W} {W′} {α} {A} {c} {θ} {V} {V′}
    {index} {result} {R} coercion =
  forward-return
    (indexed-left-generalized-instantiation
      {W = W} {W′ = W′} {α = α} {A = A}
      {c = c} {θ = θ} {V = V} {V′ = V′}
      {left-index = index} {right-index = zero}
      {result = result} {R = R}
      (forward-at-right-zero refl coercion))

left-generalized-backward-bundle :
  ∀ {W W′ α A c θ V V′ index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (immediateReturn W′ V′) index →
  TargetBlameSimulation R
    (coerceValue W (seal-name α ∷ θ) c V)
    (immediateReturn W′ V′) index →
  IndexedTerminalSimulation result R
    (instantiateValue W α (generalized A c θ V))
    (immediateReturn W′ V′)
    (suc zero) index
left-generalized-backward-bundle
    {index = index} backward blame =
  indexed-left-generalized-instantiation
    {left-index = zero} {right-index = index}
    (backward-at-left-zero refl backward blame)

directional-left-generalized-backward :
  ∀ {W W′ α A c θ V V′ index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (immediateReturn W′ V′) index →
  TargetBlameSimulation R
    (coerceValue W (seal-name α ∷ θ) c V)
    (immediateReturn W′ V′) index →
  BackwardReturnSimulation result R
    (instantiateValue W α (generalized A c θ V))
    (immediateReturn W′ V′) index
directional-left-generalized-backward backward blame =
  backward-return
    (left-generalized-backward-bundle backward blame)

directional-left-generalized-target-blame :
  ∀ {W W′ α A c θ V V′ index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (immediateReturn W′ V′) index →
  TargetBlameSimulation R
    (coerceValue W (seal-name α ∷ θ) c V)
    (immediateReturn W′ V′) index →
  TargetBlameSimulation R
    (instantiateValue W α (generalized A c θ V))
    (immediateReturn W′ V′) index
directional-left-generalized-target-blame backward blame =
  target-blame-reflects
    (left-generalized-backward-bundle backward blame)

directional-right-generalized-forward :
  ∀ {W W′ α′ A′ c′ θ′ V V′ index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  ForwardReturnSimulation result R
    (immediateReturn W V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    index →
  ForwardReturnSimulation result R
    (immediateReturn W V)
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
    index
directional-right-generalized-forward
    {W} {W′} {α′} {A′} {c′} {θ′} {V} {V′}
    {index} {result} {R} coercion =
  forward-return
    (indexed-right-generalized-instantiation
      {W = W} {W′ = W′} {α′ = α′} {A′ = A′}
      {c′ = c′} {θ′ = θ′} {V = V} {V′ = V′}
      {left-index = index} {right-index = zero}
      {result = result} {R = R}
      (forward-at-right-zero refl coercion))

directional-right-generalized-backward :
  ∀ {W W′ α′ A′ c′ θ′ V V′ index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation result R
    (immediateReturn W V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    index →
  TargetBlameSimulation R
    (immediateReturn W V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    index →
  BackwardReturnSimulation result R
    (immediateReturn W V)
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
    (suc index)
directional-right-generalized-backward
    {W} {W′} {α′} {A′} {c′} {θ′} {V} {V′}
    {index} {result} {R} backward blame =
  backward-return
    (indexed-right-generalized-instantiation
      {W = W} {W′ = W′} {α′ = α′} {A′ = A′}
      {c′ = c′} {θ′ = θ′} {V = V} {V′ = V′}
      {left-index = zero} {right-index = index}
      {result = result} {R = R}
      (backward-at-left-zero refl backward blame))

directional-right-generalized-target-blame :
  ∀ {W W′ α′ A′ c′ θ′ V V′ index}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation result R
    (immediateReturn W V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    index →
  TargetBlameSimulation R
    (immediateReturn W V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′)
    index →
  TargetBlameSimulation R
    (immediateReturn W V)
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
    (suc index)
directional-right-generalized-target-blame
    {W} {W′} {α′} {A′} {c′} {θ′} {V} {V′}
    {index} {result} {R} backward blame =
  target-blame-reflects
    (indexed-right-generalized-instantiation
      {W = W} {W′ = W′} {α′ = α′} {A′ = A′}
      {c′ = c′} {θ′ = θ′} {V = V} {V′ = V′}
      {left-index = zero} {right-index = index}
      {result = result} {R = R}
      (backward-at-left-zero refl backward blame))
