module proof.InterpreterDirectionalFunctionProxy where

-- File Charter:
--   * Derives directional application observations for paired and
--     one-sided function proxies.
--   * Reuses the checked proxy composition at a zero-index endpoint, so
--     every callback is needed only in the observed direction.
--   * Contains no interpreter recursion, reduction, or quotient argument.

open import Agda.Builtin.Equality using (refl)
open import Data.Nat using (suc; zero)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedFunctionProxy
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterDirectionalSimulation using
  (backward-at-left-zero; forward-at-right-zero)

open ITN.RelatedWorlds

directional-paired-function-proxy-forward :
  ∀ {W W′ θ θ′ p p′ q q′ V V′ U U′ index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  ForwardReturnSimulation domain-result R
    (coerceValue W θ p U)
    (coerceValue W′ θ′ p′ U′) index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    ForwardReturnSimulation application-result S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    ForwardReturnSimulation result S
      (coerceValue Z θ q P)
      (coerceValue Z′ θ′ q′ P′) index) →
  ForwardReturnSimulation result R
    (applyValue W (function-proxy p q θ V) U)
    (applyValue W′ (function-proxy p′ q′ θ′ V′) U′)
    (suc index)
directional-paired-function-proxy-forward
    {index = index} domain application codomain =
  forward-return
    (indexed-paired-function-proxy-application
      {left-index = index} {right-index = zero}
      (forward-at-right-zero refl domain)
      (λ R≤S Q~Q′ →
        forward-at-right-zero refl (application R≤S Q~Q′))
      (λ R≤S P~P′ →
        forward-at-right-zero refl (codomain R≤S P~P′)))

paired-function-proxy-backward-bundle :
  ∀ {W W′ θ θ′ p p′ q q′ V V′ U U′ index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation domain-result R
    (coerceValue W θ p U)
    (coerceValue W′ θ′ p′ U′) index →
  TargetBlameSimulation R
    (coerceValue W θ p U)
    (coerceValue W′ θ′ p′ U′) index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    BackwardReturnSimulation application-result S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    TargetBlameSimulation S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    BackwardReturnSimulation result S
      (coerceValue Z θ q P)
      (coerceValue Z′ θ′ q′ P′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    TargetBlameSimulation S
      (coerceValue Z θ q P)
      (coerceValue Z′ θ′ q′ P′) index) →
  IndexedTerminalSimulation result R
    (applyValue W (function-proxy p q θ V) U)
    (applyValue W′ (function-proxy p′ q′ θ′ V′) U′)
    (suc zero) (suc index)
paired-function-proxy-backward-bundle
    {index = index}
    domain-backward domain-blame
    application-backward application-blame
    codomain-backward codomain-blame =
  indexed-paired-function-proxy-application
    {left-index = zero} {right-index = index}
    (backward-at-left-zero refl domain-backward domain-blame)
    (λ R≤S Q~Q′ →
      backward-at-left-zero refl
        (application-backward R≤S Q~Q′)
        (application-blame R≤S Q~Q′))
    (λ R≤S P~P′ →
      backward-at-left-zero refl
        (codomain-backward R≤S P~P′)
        (codomain-blame R≤S P~P′))

directional-paired-function-proxy-backward :
  ∀ {W W′ θ θ′ p p′ q q′ V V′ U U′ index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation domain-result R
    (coerceValue W θ p U)
    (coerceValue W′ θ′ p′ U′) index →
  TargetBlameSimulation R
    (coerceValue W θ p U)
    (coerceValue W′ θ′ p′ U′) index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    BackwardReturnSimulation application-result S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    TargetBlameSimulation S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    BackwardReturnSimulation result S
      (coerceValue Z θ q P)
      (coerceValue Z′ θ′ q′ P′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    TargetBlameSimulation S
      (coerceValue Z θ q P)
      (coerceValue Z′ θ′ q′ P′) index) →
  BackwardReturnSimulation result R
    (applyValue W (function-proxy p q θ V) U)
    (applyValue W′ (function-proxy p′ q′ θ′ V′) U′)
    (suc index)
directional-paired-function-proxy-backward
    {W} {W′} {θ} {θ′} {p} {p′} {q} {q′}
    {V} {V′} {U} {U′} {index}
    {domain-result} {application-result} {result} {R}
    domain-backward domain-blame
    application-backward application-blame
    codomain-backward codomain-blame =
  backward-return
    (paired-function-proxy-backward-bundle
      {W = W} {W′ = W′} {θ = θ} {θ′ = θ′}
      {p = p} {p′ = p′} {q = q} {q′ = q′}
      {V = V} {V′ = V′} {U = U} {U′ = U′}
      {index = index}
      {domain-result = domain-result}
      {application-result = application-result}
      {result = result} {R = R}
      domain-backward domain-blame
      application-backward application-blame
      codomain-backward codomain-blame)

directional-paired-function-proxy-target-blame :
  ∀ {W W′ θ θ′ p p′ q q′ V V′ U U′ index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation domain-result R
    (coerceValue W θ p U)
    (coerceValue W′ θ′ p′ U′) index →
  TargetBlameSimulation R
    (coerceValue W θ p U)
    (coerceValue W′ θ′ p′ U′) index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    BackwardReturnSimulation application-result S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    TargetBlameSimulation S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    BackwardReturnSimulation result S
      (coerceValue Z θ q P)
      (coerceValue Z′ θ′ q′ P′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    TargetBlameSimulation S
      (coerceValue Z θ q P)
      (coerceValue Z′ θ′ q′ P′) index) →
  TargetBlameSimulation R
    (applyValue W (function-proxy p q θ V) U)
    (applyValue W′ (function-proxy p′ q′ θ′ V′) U′)
    (suc index)
directional-paired-function-proxy-target-blame
    {W} {W′} {θ} {θ′} {p} {p′} {q} {q′}
    {V} {V′} {U} {U′} {index}
    {domain-result} {application-result} {result} {R}
    domain-backward domain-blame
    application-backward application-blame
    codomain-backward codomain-blame =
  target-blame-reflects
    (paired-function-proxy-backward-bundle
      {W = W} {W′ = W′} {θ = θ} {θ′ = θ′}
      {p = p} {p′ = p′} {q = q} {q′ = q′}
      {V = V} {V′ = V′} {U = U} {U′ = U′}
      {index = index}
      {domain-result = domain-result}
      {application-result = application-result}
      {result = result} {R = R}
      domain-backward domain-blame
      application-backward application-blame
      codomain-backward codomain-blame)

directional-left-function-proxy-forward :
  ∀ {W W′ θ p q V V′ U U′ index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  ForwardReturnSimulation domain-result R
    (coerceValue W θ p U) (immediateReturn W′ U′) index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    ForwardReturnSimulation application-result S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    ForwardReturnSimulation result S
      (coerceValue Z θ q P) (immediateReturn Z′ P′) index) →
  ForwardReturnSimulation result R
    (applyValue W (function-proxy p q θ V) U)
    (applyValue W′ V′ U′) (suc index)
directional-left-function-proxy-forward
    {index = index} domain application codomain =
  forward-return
    (indexed-left-function-proxy-application
      {left-index = index} {right-index = zero}
      (forward-at-right-zero refl domain)
      (λ R≤S Q~Q′ →
        forward-at-right-zero refl (application R≤S Q~Q′))
      (λ R≤S P~P′ →
        forward-at-right-zero refl (codomain R≤S P~P′)))

left-function-proxy-backward-bundle :
  ∀ {W W′ θ p q V V′ U U′ index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation domain-result R
    (coerceValue W θ p U) (immediateReturn W′ U′) index →
  TargetBlameSimulation R
    (coerceValue W θ p U) (immediateReturn W′ U′) index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    BackwardReturnSimulation application-result S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    TargetBlameSimulation S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    BackwardReturnSimulation result S
      (coerceValue Z θ q P) (immediateReturn Z′ P′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    TargetBlameSimulation S
      (coerceValue Z θ q P) (immediateReturn Z′ P′) index) →
  IndexedTerminalSimulation result R
    (applyValue W (function-proxy p q θ V) U)
    (applyValue W′ V′ U′) (suc zero) index
left-function-proxy-backward-bundle
    {index = index}
    domain-backward domain-blame
    application-backward application-blame
    codomain-backward codomain-blame =
  indexed-left-function-proxy-application
    {left-index = zero} {right-index = index}
    (backward-at-left-zero refl domain-backward domain-blame)
    (λ R≤S Q~Q′ →
      backward-at-left-zero refl
        (application-backward R≤S Q~Q′)
        (application-blame R≤S Q~Q′))
    (λ R≤S P~P′ →
      backward-at-left-zero refl
        (codomain-backward R≤S P~P′)
        (codomain-blame R≤S P~P′))

directional-left-function-proxy-backward :
  ∀ {W W′ θ p q V V′ U U′ index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation domain-result R
    (coerceValue W θ p U) (immediateReturn W′ U′) index →
  TargetBlameSimulation R
    (coerceValue W θ p U) (immediateReturn W′ U′) index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    BackwardReturnSimulation application-result S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    TargetBlameSimulation S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    BackwardReturnSimulation result S
      (coerceValue Z θ q P) (immediateReturn Z′ P′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    TargetBlameSimulation S
      (coerceValue Z θ q P) (immediateReturn Z′ P′) index) →
  BackwardReturnSimulation result R
    (applyValue W (function-proxy p q θ V) U)
    (applyValue W′ V′ U′) index
directional-left-function-proxy-backward
    {W} {W′} {θ} {p} {q} {V} {V′} {U} {U′} {index}
    {domain-result} {application-result} {result} {R}
    domain-backward domain-blame
    application-backward application-blame
    codomain-backward codomain-blame =
  backward-return
    (left-function-proxy-backward-bundle
      {W = W} {W′ = W′} {θ = θ} {p = p} {q = q}
      {V = V} {V′ = V′} {U = U} {U′ = U′}
      {index = index}
      {domain-result = domain-result}
      {application-result = application-result}
      {result = result} {R = R}
      domain-backward domain-blame
      application-backward application-blame
      codomain-backward codomain-blame)

directional-left-function-proxy-target-blame :
  ∀ {W W′ θ p q V V′ U U′ index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation domain-result R
    (coerceValue W θ p U) (immediateReturn W′ U′) index →
  TargetBlameSimulation R
    (coerceValue W θ p U) (immediateReturn W′ U′) index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    BackwardReturnSimulation application-result S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    TargetBlameSimulation S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    BackwardReturnSimulation result S
      (coerceValue Z θ q P) (immediateReturn Z′ P′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    TargetBlameSimulation S
      (coerceValue Z θ q P) (immediateReturn Z′ P′) index) →
  TargetBlameSimulation R
    (applyValue W (function-proxy p q θ V) U)
    (applyValue W′ V′ U′) index
directional-left-function-proxy-target-blame
    {W} {W′} {θ} {p} {q} {V} {V′} {U} {U′} {index}
    {domain-result} {application-result} {result} {R}
    domain-backward domain-blame
    application-backward application-blame
    codomain-backward codomain-blame =
  target-blame-reflects
    (left-function-proxy-backward-bundle
      {W = W} {W′ = W′} {θ = θ} {p = p} {q = q}
      {V = V} {V′ = V′} {U = U} {U′ = U′}
      {index = index}
      {domain-result = domain-result}
      {application-result = application-result}
      {result = result} {R = R}
      domain-backward domain-blame
      application-backward application-blame
      codomain-backward codomain-blame)

directional-right-function-proxy-forward :
  ∀ {W W′ θ′ p′ q′ V V′ U U′ index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  ForwardReturnSimulation domain-result R
    (immediateReturn W U) (coerceValue W′ θ′ p′ U′) index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    ForwardReturnSimulation application-result S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    ForwardReturnSimulation result S
      (immediateReturn Z P) (coerceValue Z′ θ′ q′ P′) index) →
  ForwardReturnSimulation result R
    (applyValue W V U)
    (applyValue W′ (function-proxy p′ q′ θ′ V′) U′)
    index
directional-right-function-proxy-forward
    {index = index} domain application codomain =
  forward-return
    (indexed-right-function-proxy-application
      {left-index = index} {right-index = zero}
      (forward-at-right-zero refl domain)
      (λ R≤S Q~Q′ →
        forward-at-right-zero refl (application R≤S Q~Q′))
      (λ R≤S P~P′ →
        forward-at-right-zero refl (codomain R≤S P~P′)))

right-function-proxy-backward-bundle :
  ∀ {W W′ θ′ p′ q′ V V′ U U′ index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation domain-result R
    (immediateReturn W U) (coerceValue W′ θ′ p′ U′) index →
  TargetBlameSimulation R
    (immediateReturn W U) (coerceValue W′ θ′ p′ U′) index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    BackwardReturnSimulation application-result S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    TargetBlameSimulation S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    BackwardReturnSimulation result S
      (immediateReturn Z P) (coerceValue Z′ θ′ q′ P′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    TargetBlameSimulation S
      (immediateReturn Z P) (coerceValue Z′ θ′ q′ P′) index) →
  IndexedTerminalSimulation result R
    (applyValue W V U)
    (applyValue W′ (function-proxy p′ q′ θ′ V′) U′)
    zero (suc index)
right-function-proxy-backward-bundle
    {index = index}
    domain-backward domain-blame
    application-backward application-blame
    codomain-backward codomain-blame =
  indexed-right-function-proxy-application
    {left-index = zero} {right-index = index}
    (backward-at-left-zero refl domain-backward domain-blame)
    (λ R≤S Q~Q′ →
      backward-at-left-zero refl
        (application-backward R≤S Q~Q′)
        (application-blame R≤S Q~Q′))
    (λ R≤S P~P′ →
      backward-at-left-zero refl
        (codomain-backward R≤S P~P′)
        (codomain-blame R≤S P~P′))

directional-right-function-proxy-backward :
  ∀ {W W′ θ′ p′ q′ V V′ U U′ index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation domain-result R
    (immediateReturn W U) (coerceValue W′ θ′ p′ U′) index →
  TargetBlameSimulation R
    (immediateReturn W U) (coerceValue W′ θ′ p′ U′) index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    BackwardReturnSimulation application-result S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    TargetBlameSimulation S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    BackwardReturnSimulation result S
      (immediateReturn Z P) (coerceValue Z′ θ′ q′ P′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    TargetBlameSimulation S
      (immediateReturn Z P) (coerceValue Z′ θ′ q′ P′) index) →
  BackwardReturnSimulation result R
    (applyValue W V U)
    (applyValue W′ (function-proxy p′ q′ θ′ V′) U′)
    (suc index)
directional-right-function-proxy-backward
    {W} {W′} {θ′} {p′} {q′} {V} {V′} {U} {U′} {index}
    {domain-result} {application-result} {result} {R}
    domain-backward domain-blame
    application-backward application-blame
    codomain-backward codomain-blame =
  backward-return
    (right-function-proxy-backward-bundle
      {W = W} {W′ = W′} {θ′ = θ′} {p′ = p′} {q′ = q′}
      {V = V} {V′ = V′} {U = U} {U′ = U′}
      {index = index}
      {domain-result = domain-result}
      {application-result = application-result}
      {result = result} {R = R}
      domain-backward domain-blame
      application-backward application-blame
      codomain-backward codomain-blame)

directional-right-function-proxy-target-blame :
  ∀ {W W′ θ′ p′ q′ V V′ U U′ index}
    {domain-result application-result result :
      ValueResultRelation}
    {R : WorldRelation W W′} →
  BackwardReturnSimulation domain-result R
    (immediateReturn W U) (coerceValue W′ θ′ p′ U′) index →
  TargetBlameSimulation R
    (immediateReturn W U) (coerceValue W′ θ′ p′ U′) index →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    BackwardReturnSimulation application-result S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ Q Q′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    domain-result S Q Q′ →
    TargetBlameSimulation S
      (applyValue Z V Q) (applyValue Z′ V′ Q′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    BackwardReturnSimulation result S
      (immediateReturn Z P) (coerceValue Z′ θ′ q′ P′) index) →
  (∀ {Z Z′ P P′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    application-result S P P′ →
    TargetBlameSimulation S
      (immediateReturn Z P) (coerceValue Z′ θ′ q′ P′) index) →
  TargetBlameSimulation R
    (applyValue W V U)
    (applyValue W′ (function-proxy p′ q′ θ′ V′) U′)
    (suc index)
directional-right-function-proxy-target-blame
    {W} {W′} {θ′} {p′} {q′} {V} {V′} {U} {U′} {index}
    {domain-result} {application-result} {result} {R}
    domain-backward domain-blame
    application-backward application-blame
    codomain-backward codomain-blame =
  target-blame-reflects
    (right-function-proxy-backward-bundle
      {W = W} {W′ = W′} {θ′ = θ′} {p′ = p′} {q′ = q′}
      {V = V} {V′ = V′} {U = U} {U′ = U′}
      {index = index}
      {domain-result = domain-result}
      {application-result = application-result}
      {result = result} {R = R}
      domain-backward domain-blame
      application-backward application-blame
      codomain-backward codomain-blame)
