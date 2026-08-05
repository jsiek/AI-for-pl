module proof.InterpreterDirectionalSequence where

-- File Charter:
--   * Composes forward return, backward return, and target-blame
--     observations through paired interpreter sequencing.
--   * Reuses the checked indexed sequencing proof after filling only the
--     irrelevant zero-fuel endpoint observations.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (suc; zero)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterDirectionalSimulation using
  (backward-at-left-zero; forward-at-right-zero)
open import proof.InterpreterIndexedChainSimulation using
  (indexed-chain-simulation)
open import proof.InterpreterIndexedOneSidedSequenceSimulation using
  (indexed-left-chain-simulation)
open import proof.InterpreterIndexedRightSequenceSimulation using
  (indexed-right-chain-simulation)
open import proof.InterpreterIndexedSequenceSimulation using
  ( indexed-sequence-backward
  ; indexed-sequence-forward
  ; indexed-sequence-target-blame
  )

open ITN.RelatedWorlds

directional-sequence-forward :
  ∀ {W W′ left-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  ForwardReturnSimulation
    head-result R left-head right-head left-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    ForwardReturnSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′) left-index) →
  right-head zero ≡ timed W′ →
  (∀ U′ V′ →
    right-continuation U′ V′ zero ≡ timed U′) →
  TerminalStable right-head →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  ForwardReturnSimulation continuation-result R
    (sequence W left-head left-continuation)
    (sequence W′ right-head right-continuation)
    (suc left-index)
directional-sequence-forward
    {W} {W′} {left-index}
    {head-result} {continuation-result} {R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-forward continuation-forward
    right-head-zero right-continuation-zero
    right-head-stable right-continuation-stable =
  indexed-sequence-forward
    {W = W} {W′ = W′}
    {left-index = left-index} {right-index = zero}
    {head-result = head-result}
    {continuation-result = continuation-result}
    {R = R} {left-head = left-head}
    {right-head = right-head}
    {left-continuation = left-continuation}
    {right-continuation = right-continuation}
    (forward-at-right-zero
      {left = left-head} {right = right-head}
      right-head-zero head-forward)
    (λ {U} {U′} {V} {V′} {S} R≤S V~V′ →
      forward-at-right-zero
        {R = S}
        {left = left-continuation U V}
        {right = right-continuation U′ V′}
        (right-continuation-zero _ _)
        (continuation-forward R≤S V~V′))
    right-head-stable right-continuation-stable

directional-sequence-backward :
  ∀ {W W′ right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  BackwardReturnSimulation
    head-result R left-head right-head right-index →
  TargetBlameSimulation R left-head right-head right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    BackwardReturnSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′) right-index) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TargetBlameSimulation S
      (left-continuation U V)
      (right-continuation U′ V′) right-index) →
  left-head zero ≡ timed W →
  (∀ U V →
    left-continuation U V zero ≡ timed U) →
  TerminalStable left-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  BackwardReturnSimulation continuation-result R
    (sequence W left-head left-continuation)
    (sequence W′ right-head right-continuation)
    (suc right-index)
directional-sequence-backward
    {W} {W′} {right-index}
    {head-result} {continuation-result} {R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-backward head-blame
    continuation-backward continuation-blame
    left-head-zero left-continuation-zero
    left-head-stable left-continuation-stable =
  indexed-sequence-backward
    {W = W} {W′ = W′}
    {left-index = zero} {right-index = right-index}
    {head-result = head-result}
    {continuation-result = continuation-result}
    {R = R} {left-head = left-head}
    {right-head = right-head}
    {left-continuation = left-continuation}
    {right-continuation = right-continuation}
    (backward-at-left-zero
      {left = left-head} {right = right-head}
      left-head-zero head-backward head-blame)
    (λ {U} {U′} {V} {V′} {S} R≤S V~V′ →
      backward-at-left-zero
        {R = S}
        {left = left-continuation U V}
        {right = right-continuation U′ V′}
        (left-continuation-zero _ _)
        (continuation-backward R≤S V~V′)
        (continuation-blame R≤S V~V′))
    left-head-stable left-continuation-stable

directional-sequence-target-blame :
  ∀ {W W′ right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  BackwardReturnSimulation
    head-result R left-head right-head right-index →
  TargetBlameSimulation R left-head right-head right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    BackwardReturnSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′) right-index) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TargetBlameSimulation S
      (left-continuation U V)
      (right-continuation U′ V′) right-index) →
  left-head zero ≡ timed W →
  (∀ U V →
    left-continuation U V zero ≡ timed U) →
  TerminalStable left-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  TargetBlameSimulation R
    (sequence W left-head left-continuation)
    (sequence W′ right-head right-continuation)
    (suc right-index)
directional-sequence-target-blame
    {W} {W′} {right-index}
    {head-result} {continuation-result} {R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-backward head-blame
    continuation-backward continuation-blame
    left-head-zero left-continuation-zero
    left-head-stable left-continuation-stable =
  indexed-sequence-target-blame
    {W = W} {W′ = W′}
    {left-index = zero} {right-index = right-index}
    {head-result = head-result}
    {continuation-result = continuation-result}
    {R = R} {left-head = left-head}
    {right-head = right-head}
    {left-continuation = left-continuation}
    {right-continuation = right-continuation}
    (backward-at-left-zero
      {left = left-head} {right = right-head}
      left-head-zero head-backward head-blame)
    (λ {U} {U′} {V} {V′} {S} R≤S V~V′ →
      backward-at-left-zero
        {R = S}
        {left = left-continuation U V}
        {right = right-continuation U′ V′}
        (left-continuation-zero _ _)
        (continuation-backward R≤S V~V′)
        (continuation-blame R≤S V~V′))
    left-head-stable left-continuation-stable

directional-chain-forward :
  ∀ {W W′ left-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  ForwardReturnSimulation
    head-result R left-head right-head left-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    ForwardReturnSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′) left-index) →
  right-head zero ≡ timed W′ →
  (∀ U′ V′ →
    right-continuation U′ V′ zero ≡ timed U′) →
  TerminalStable left-head →
  TerminalStable right-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  ForwardReturnSimulation continuation-result R
    (chain left-head left-continuation)
    (chain right-head right-continuation)
    left-index
directional-chain-forward
    {W} {W′} {left-index}
    {head-result} {continuation-result} {R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-forward continuation-forward
    right-head-zero right-continuation-zero
    left-head-stable right-head-stable
    left-continuation-stable right-continuation-stable =
  forward-return
    (indexed-chain-simulation
      {W = W} {W′ = W′}
      {left-index = left-index} {right-index = zero}
      {head-result = head-result}
      {continuation-result = continuation-result}
      {R = R} {left-head = left-head}
      {right-head = right-head}
      {left-continuation = left-continuation}
      {right-continuation = right-continuation}
      (forward-at-right-zero
        {left = left-head} {right = right-head}
        right-head-zero head-forward)
      (λ {U} {U′} {V} {V′} {S} R≤S V~V′ →
        forward-at-right-zero
          {R = S}
          {left = left-continuation U V}
          {right = right-continuation U′ V′}
          (right-continuation-zero _ _)
          (continuation-forward R≤S V~V′))
      left-head-stable right-head-stable
      left-continuation-stable right-continuation-stable)

directional-chain-backward :
  ∀ {W W′ right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  BackwardReturnSimulation
    head-result R left-head right-head right-index →
  TargetBlameSimulation R left-head right-head right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    BackwardReturnSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′) right-index) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TargetBlameSimulation S
      (left-continuation U V)
      (right-continuation U′ V′) right-index) →
  left-head zero ≡ timed W →
  (∀ U V →
    left-continuation U V zero ≡ timed U) →
  TerminalStable left-head →
  TerminalStable right-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  BackwardReturnSimulation continuation-result R
    (chain left-head left-continuation)
    (chain right-head right-continuation)
    right-index
directional-chain-backward
    {W} {W′} {right-index}
    {head-result} {continuation-result} {R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-backward head-blame
    continuation-backward continuation-blame
    left-head-zero left-continuation-zero
    left-head-stable right-head-stable
    left-continuation-stable right-continuation-stable =
  backward-return
    (indexed-chain-simulation
      {W = W} {W′ = W′}
      {left-index = zero} {right-index = right-index}
      {head-result = head-result}
      {continuation-result = continuation-result}
      {R = R} {left-head = left-head}
      {right-head = right-head}
      {left-continuation = left-continuation}
      {right-continuation = right-continuation}
      (backward-at-left-zero
        {left = left-head} {right = right-head}
        left-head-zero head-backward head-blame)
      (λ {U} {U′} {V} {V′} {S} R≤S V~V′ →
        backward-at-left-zero
          {R = S}
          {left = left-continuation U V}
          {right = right-continuation U′ V′}
          (left-continuation-zero _ _)
          (continuation-backward R≤S V~V′)
          (continuation-blame R≤S V~V′))
      left-head-stable right-head-stable
      left-continuation-stable right-continuation-stable)

directional-chain-target-blame :
  ∀ {W W′ right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  BackwardReturnSimulation
    head-result R left-head right-head right-index →
  TargetBlameSimulation R left-head right-head right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    BackwardReturnSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′) right-index) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TargetBlameSimulation S
      (left-continuation U V)
      (right-continuation U′ V′) right-index) →
  left-head zero ≡ timed W →
  (∀ U V →
    left-continuation U V zero ≡ timed U) →
  TerminalStable left-head →
  TerminalStable right-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  TargetBlameSimulation R
    (chain left-head left-continuation)
    (chain right-head right-continuation)
    right-index
directional-chain-target-blame
    {W} {W′} {right-index}
    {head-result} {continuation-result} {R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-backward head-blame
    continuation-backward continuation-blame
    left-head-zero left-continuation-zero
    left-head-stable right-head-stable
    left-continuation-stable right-continuation-stable =
  target-blame-reflects
    (indexed-chain-simulation
      {W = W} {W′ = W′}
      {left-index = zero} {right-index = right-index}
      {head-result = head-result}
      {continuation-result = continuation-result}
      {R = R} {left-head = left-head}
      {right-head = right-head}
      {left-continuation = left-continuation}
      {right-continuation = right-continuation}
      (backward-at-left-zero
        {left = left-head} {right = right-head}
        left-head-zero head-backward head-blame)
      (λ {U} {U′} {V} {V′} {S} R≤S V~V′ →
        backward-at-left-zero
          {R = S}
          {left = left-continuation U V}
          {right = right-continuation U′ V′}
          (left-continuation-zero _ _)
          (continuation-backward R≤S V~V′)
          (continuation-blame R≤S V~V′))
      left-head-stable right-head-stable
      left-continuation-stable right-continuation-stable)

directional-left-chain-forward :
  ∀ {W W′ left-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation : World → Value → Computation} →
  ForwardReturnSimulation
    head-result R left-head right-head left-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    ForwardReturnSimulation continuation-result S
      (left-continuation U V)
      (immediateReturn U′ V′) left-index) →
  right-head zero ≡ timed W′ →
  TerminalStable left-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  ForwardReturnSimulation continuation-result R
    (chain left-head left-continuation)
    right-head left-index
directional-left-chain-forward
    {W} {W′} {left-index}
    {head-result} {continuation-result} {R}
    {left-head} {right-head} {left-continuation}
    head-forward continuation-forward right-zero
    left-stable continuation-stable =
  forward-return
    (indexed-left-chain-simulation
      {W = W} {W′ = W′}
      {left-index = left-index} {right-index = zero}
      {head-result = head-result}
      {continuation-result = continuation-result}
      {R = R} {left-head = left-head}
      {right-head = right-head}
      {left-continuation = left-continuation}
      (forward-at-right-zero right-zero head-forward)
      (λ R≤S V~V′ →
        forward-at-right-zero refl
          (continuation-forward R≤S V~V′))
      left-stable continuation-stable right-zero)

directional-left-chain-backward :
  ∀ {W W′ right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation : World → Value → Computation} →
  BackwardReturnSimulation
    head-result R left-head right-head right-index →
  TargetBlameSimulation R left-head right-head right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    BackwardReturnSimulation continuation-result S
      (left-continuation U V)
      (immediateReturn U′ V′) right-index) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TargetBlameSimulation S
      (left-continuation U V)
      (immediateReturn U′ V′) right-index) →
  left-head zero ≡ timed W →
  (∀ U V → left-continuation U V zero ≡ timed U) →
  TerminalStable left-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  right-head zero ≡ timed W′ →
  BackwardReturnSimulation continuation-result R
    (chain left-head left-continuation)
    right-head right-index
directional-left-chain-backward
    {W} {W′} {right-index}
    {head-result} {continuation-result} {R}
    {left-head} {right-head} {left-continuation}
    head-backward head-blame
    continuation-backward continuation-blame
    left-zero continuation-zero
    left-stable continuation-stable right-zero =
  backward-return
    (indexed-left-chain-simulation
      {W = W} {W′ = W′}
      {left-index = zero} {right-index = right-index}
      {head-result = head-result}
      {continuation-result = continuation-result}
      {R = R} {left-head = left-head}
      {right-head = right-head}
      {left-continuation = left-continuation}
      (backward-at-left-zero
        left-zero head-backward head-blame)
      (λ R≤S V~V′ →
        backward-at-left-zero
          (continuation-zero _ _)
          (continuation-backward R≤S V~V′)
          (continuation-blame R≤S V~V′))
      left-stable continuation-stable right-zero)

directional-left-chain-target-blame :
  ∀ {W W′ right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation : World → Value → Computation} →
  BackwardReturnSimulation
    head-result R left-head right-head right-index →
  TargetBlameSimulation R left-head right-head right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    BackwardReturnSimulation continuation-result S
      (left-continuation U V)
      (immediateReturn U′ V′) right-index) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TargetBlameSimulation S
      (left-continuation U V)
      (immediateReturn U′ V′) right-index) →
  left-head zero ≡ timed W →
  (∀ U V → left-continuation U V zero ≡ timed U) →
  TerminalStable left-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  right-head zero ≡ timed W′ →
  TargetBlameSimulation R
    (chain left-head left-continuation)
    right-head right-index
directional-left-chain-target-blame
    {W} {W′} {right-index}
    {head-result} {continuation-result} {R}
    {left-head} {right-head} {left-continuation}
    head-backward head-blame
    continuation-backward continuation-blame
    left-zero continuation-zero
    left-stable continuation-stable right-zero =
  target-blame-reflects
    (indexed-left-chain-simulation
      {W = W} {W′ = W′}
      {left-index = zero} {right-index = right-index}
      {head-result = head-result}
      {continuation-result = continuation-result}
      {R = R} {left-head = left-head}
      {right-head = right-head}
      {left-continuation = left-continuation}
      (backward-at-left-zero
        left-zero head-backward head-blame)
      (λ R≤S V~V′ →
        backward-at-left-zero
          (continuation-zero _ _)
          (continuation-backward R≤S V~V′)
          (continuation-blame R≤S V~V′))
      left-stable continuation-stable right-zero)

directional-right-chain-forward :
  ∀ {W W′ left-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {right-continuation : World → Value → Computation} →
  ForwardReturnSimulation
    head-result R left-head right-head left-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    ForwardReturnSimulation continuation-result S
      (immediateReturn U V)
      (right-continuation U′ V′) left-index) →
  left-head zero ≡ timed W →
  right-head zero ≡ timed W′ →
  (∀ U′ V′ → right-continuation U′ V′ zero ≡ timed U′) →
  TerminalStable right-head →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  ForwardReturnSimulation continuation-result R
    left-head (chain right-head right-continuation) left-index
directional-right-chain-forward
    {W} {W′} {left-index}
    {head-result} {continuation-result} {R}
    {left-head} {right-head} {right-continuation}
    head-forward continuation-forward
    left-zero right-zero continuation-zero
    right-stable continuation-stable =
  forward-return
    (indexed-right-chain-simulation
      {W = W} {W′ = W′}
      {left-index = left-index} {right-index = zero}
      {head-result = head-result}
      {continuation-result = continuation-result}
      {R = R} {left-head = left-head}
      {right-head = right-head}
      {right-continuation = right-continuation}
      (forward-at-right-zero right-zero head-forward)
      (λ R≤S V~V′ →
        forward-at-right-zero
          (continuation-zero _ _)
          (continuation-forward R≤S V~V′))
      left-zero right-stable continuation-stable)

directional-right-chain-backward :
  ∀ {W W′ right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {right-continuation : World → Value → Computation} →
  BackwardReturnSimulation
    head-result R left-head right-head right-index →
  TargetBlameSimulation R left-head right-head right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    BackwardReturnSimulation continuation-result S
      (immediateReturn U V)
      (right-continuation U′ V′) right-index) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TargetBlameSimulation S
      (immediateReturn U V)
      (right-continuation U′ V′) right-index) →
  left-head zero ≡ timed W →
  TerminalStable right-head →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  BackwardReturnSimulation continuation-result R
    left-head (chain right-head right-continuation) right-index
directional-right-chain-backward
    {W} {W′} {right-index}
    {head-result} {continuation-result} {R}
    {left-head} {right-head} {right-continuation}
    head-backward head-blame
    continuation-backward continuation-blame
    left-zero right-stable continuation-stable =
  backward-return
    (indexed-right-chain-simulation
      {W = W} {W′ = W′}
      {left-index = zero} {right-index = right-index}
      {head-result = head-result}
      {continuation-result = continuation-result}
      {R = R} {left-head = left-head}
      {right-head = right-head}
      {right-continuation = right-continuation}
      (backward-at-left-zero
        left-zero head-backward head-blame)
      (λ R≤S V~V′ →
        backward-at-left-zero refl
          (continuation-backward R≤S V~V′)
          (continuation-blame R≤S V~V′))
      left-zero right-stable continuation-stable)

directional-right-chain-target-blame :
  ∀ {W W′ right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {right-continuation : World → Value → Computation} →
  BackwardReturnSimulation
    head-result R left-head right-head right-index →
  TargetBlameSimulation R left-head right-head right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    BackwardReturnSimulation continuation-result S
      (immediateReturn U V)
      (right-continuation U′ V′) right-index) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TargetBlameSimulation S
      (immediateReturn U V)
      (right-continuation U′ V′) right-index) →
  left-head zero ≡ timed W →
  TerminalStable right-head →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  TargetBlameSimulation R
    left-head (chain right-head right-continuation) right-index
directional-right-chain-target-blame
    {W} {W′} {right-index}
    {head-result} {continuation-result} {R}
    {left-head} {right-head} {right-continuation}
    head-backward head-blame
    continuation-backward continuation-blame
    left-zero right-stable continuation-stable =
  target-blame-reflects
    (indexed-right-chain-simulation
      {W = W} {W′ = W′}
      {left-index = zero} {right-index = right-index}
      {head-result = head-result}
      {continuation-result = continuation-result}
      {R = R} {left-head = left-head}
      {right-head = right-head}
      {right-continuation = right-continuation}
      (backward-at-left-zero
        left-zero head-backward head-blame)
      (λ R≤S V~V′ →
        backward-at-left-zero refl
          (continuation-backward R≤S V~V′)
          (continuation-blame R≤S V~V′))
      left-zero right-stable continuation-stable)
