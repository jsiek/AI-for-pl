module proof.InterpreterDirectionalGuard where

-- File Charter:
--   * Lifts directional terminal observations through paired and one-sided
--     fuel guards.
--   * Fills the unused endpoint at fuel zero before reusing the checked
--     indexed guard algebra.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (suc; zero)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterDirectionalSimulation using
  (backward-at-left-zero; forward-at-right-zero)
open import proof.InterpreterIndexedGuardSimulation using
  (left-guard-indexed; paired-guard-indexed; right-guard-indexed)

open ITN.RelatedWorlds

paired-guard-forward :
  ∀ {W W′ U U′ left-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  right zero ≡ timed W′ →
  ForwardReturnSimulation
    value-result R left right left-index →
  ForwardReturnSimulation value-result R
    (guard U left) (guard U′ right) (suc left-index)
paired-guard-forward
    {U = U} {U′} {left-index}
    {value-result} {R} {left} {right}
    right-zero forward =
  forward-return
    (paired-guard-indexed
      {U = U} {U′ = U′} {left-index = left-index}
      {right-index = zero}
      (forward-at-right-zero
        {value-result = value-result} {R = R}
        {left = left} {right = right}
        right-zero forward))

paired-guard-backward :
  ∀ {W W′ U U′ right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  left zero ≡ timed W →
  BackwardReturnSimulation
    value-result R left right right-index →
  TargetBlameSimulation R left right right-index →
  BackwardReturnSimulation value-result R
    (guard U left) (guard U′ right) (suc right-index)
paired-guard-backward
    {U = U} {U′} {right-index}
    {value-result} {R} {left} {right}
    left-zero backward blame =
  backward-return
    (paired-guard-indexed
      {U = U} {U′ = U′} {left-index = zero}
      {right-index = right-index}
      (backward-at-left-zero
        {value-result = value-result} {R = R}
        {left = left} {right = right}
        left-zero backward blame))

paired-guard-target-blame :
  ∀ {W W′ U U′ right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  left zero ≡ timed W →
  BackwardReturnSimulation
    value-result R left right right-index →
  TargetBlameSimulation R left right right-index →
  TargetBlameSimulation R
    (guard U left) (guard U′ right) (suc right-index)
paired-guard-target-blame
    {U = U} {U′} {right-index}
    {value-result} {R} {left} {right}
    left-zero backward blame =
  target-blame-reflects
    (paired-guard-indexed
      {U = U} {U′ = U′} {left-index = zero}
      {right-index = right-index}
      (backward-at-left-zero
        {value-result = value-result} {R = R}
        {left = left} {right = right}
        left-zero backward blame))

left-guard-forward :
  ∀ {W W′ U left-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  right zero ≡ timed W′ →
  ForwardReturnSimulation
    value-result R left right left-index →
  ForwardReturnSimulation value-result R
    (guard U left) right (suc left-index)
left-guard-forward
    {U = U} {left-index}
    {value-result} {R} {left} {right}
    right-zero forward =
  forward-return
    (left-guard-indexed
      {U = U} {left-index = left-index}
      {right-index = zero}
      (forward-at-right-zero
        {value-result = value-result} {R = R}
        {left = left} {right = right}
        right-zero forward))

left-guard-backward :
  ∀ {W W′ U right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  left zero ≡ timed W →
  BackwardReturnSimulation
    value-result R left right right-index →
  TargetBlameSimulation R left right right-index →
  BackwardReturnSimulation value-result R
    (guard U left) right right-index
left-guard-backward
    {U = U} {right-index}
    {value-result} {R} {left} {right}
    left-zero backward blame =
  backward-return
    (left-guard-indexed
      {U = U} {left-index = zero}
      {right-index = right-index}
      (backward-at-left-zero
        {value-result = value-result} {R = R}
        {left = left} {right = right}
        left-zero backward blame))

left-guard-target-blame :
  ∀ {W W′ U right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  left zero ≡ timed W →
  BackwardReturnSimulation
    value-result R left right right-index →
  TargetBlameSimulation R left right right-index →
  TargetBlameSimulation R (guard U left) right right-index
left-guard-target-blame
    {U = U} {right-index}
    {value-result} {R} {left} {right}
    left-zero backward blame =
  target-blame-reflects
    (left-guard-indexed
      {U = U} {left-index = zero}
      {right-index = right-index}
      (backward-at-left-zero
        {value-result = value-result} {R = R}
        {left = left} {right = right}
        left-zero backward blame))

right-guard-forward :
  ∀ {W W′ U′ left-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  right zero ≡ timed W′ →
  ForwardReturnSimulation
    value-result R left right left-index →
  ForwardReturnSimulation value-result R
    left (guard U′ right) left-index
right-guard-forward
    {U′ = U′} {left-index}
    {value-result} {R} {left} {right}
    right-zero forward =
  forward-return
    (right-guard-indexed
      {U′ = U′} {left-index = left-index}
      {right-index = zero}
      (forward-at-right-zero
        {value-result = value-result} {R = R}
        {left = left} {right = right}
        right-zero forward))

right-guard-backward :
  ∀ {W W′ U′ right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  left zero ≡ timed W →
  BackwardReturnSimulation
    value-result R left right right-index →
  TargetBlameSimulation R left right right-index →
  BackwardReturnSimulation value-result R
    left (guard U′ right) (suc right-index)
right-guard-backward
    {U′ = U′} {right-index}
    {value-result} {R} {left} {right}
    left-zero backward blame =
  backward-return
    (right-guard-indexed
      {U′ = U′} {left-index = zero}
      {right-index = right-index}
      (backward-at-left-zero
        {value-result = value-result} {R = R}
        {left = left} {right = right}
        left-zero backward blame))

right-guard-target-blame :
  ∀ {W W′ U′ right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  left zero ≡ timed W →
  BackwardReturnSimulation
    value-result R left right right-index →
  TargetBlameSimulation R left right right-index →
  TargetBlameSimulation R
    left (guard U′ right) (suc right-index)
right-guard-target-blame
    {U′ = U′} {right-index}
    {value-result} {R} {left} {right}
    left-zero backward blame =
  target-blame-reflects
    (right-guard-indexed
      {U′ = U′} {left-index = zero}
      {right-index = right-index}
      (backward-at-left-zero
        {value-result = value-result} {R = R}
        {left = left} {right = right}
        left-zero backward blame))
