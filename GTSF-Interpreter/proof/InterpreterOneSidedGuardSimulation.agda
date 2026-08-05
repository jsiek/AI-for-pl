module proof.InterpreterOneSidedGuardSimulation where

-- File Charter:
--   * Adds one constructor-fuel guard to the source computation only.
--   * Shifts source terminal witnesses while leaving target witnesses intact.
--   * Uses only computation equations and terminal-simulation evidence.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Interpreter
open import Core.InterpreterOutcome
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterGuardSimulation using
  (guard-terminal-stable)

open ITN.InterpreterValues
open ITN.RelatedWorlds

left-guard-forward-return :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  ∀ {n U V} →
  guard W left n ≡ returned U V →
  Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U′ →
          Data.Product.Σ Value
            (λ V′ →
              Data.Product.Σ (WorldRelation U U′)
                (λ S →
                  WorldExtension R S ×
                  right m ≡ returned U′ V′ ×
                  value-result S V V′))))
left-guard-forward-return simulation {n = zero} ()
left-guard-forward-return simulation {n = suc n} eq =
  forward-return simulation eq

left-guard-backward-return :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  ∀ {n U′ V′} →
  right n ≡ returned U′ V′ →
  (Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U →
          Data.Product.Σ Value
            (λ V →
              Data.Product.Σ (WorldRelation U U′)
                (λ S →
                  WorldExtension R S ×
                  guard W left m ≡ returned U V ×
                  value-result S V V′)))))
  ⊎
  (Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U → guard W left m ≡ blamed U)))
left-guard-backward-return simulation eq
    with backward-return simulation eq
left-guard-backward-return simulation eq
    | inj₁ (m , U , V , S , R≤S , left-eq , V~V′) =
  inj₁ (suc m , U , V , S , R≤S , left-eq , V~V′)
left-guard-backward-return simulation eq
    | inj₂ (m , U , left-eq) =
  inj₂ (suc m , U , left-eq)

left-guard-target-blame :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  ∀ {n U′} →
  right n ≡ blamed U′ →
  Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U → guard W left m ≡ blamed U))
left-guard-target-blame simulation eq
    with target-blame-reflects simulation eq
left-guard-target-blame simulation eq
    | m , U , left-eq =
  suc m , U , left-eq

left-guard-left-error-impossible :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  ∀ {n U e} →
  guard W left n ≡ failed U e →
  ⊥
left-guard-left-error-impossible simulation {n = zero} ()
left-guard-left-error-impossible simulation {n = suc n} eq =
  left-error-impossible simulation eq

left-guard-simulation :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  TerminalSimulation value-result R (guard W left) right
left-guard-simulation
    {W} {W′} {value-result} {R} {left} {right}
    simulation =
  record
    { left-stable =
        λ { {n} {o} terminal eq k →
          guard-terminal-stable
            {W = W} {computation = left}
            (left-stable simulation)
            {n = n} {o = o} terminal eq k
          }
    ; right-stable = right-stable simulation
    ; forward-return =
        λ { {n} {U} {V} eq →
          left-guard-forward-return
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U = U} {V = V} eq
          }
    ; backward-return =
        λ { {n} {U′} {V′} eq →
          left-guard-backward-return
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U′ = U′} {V′ = V′} eq
          }
    ; target-blame-reflects =
        λ { {n} {U′} eq →
          left-guard-target-blame
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U′ = U′} eq
          }
    ; left-error-impossible =
        λ { {n} {U} {e} eq →
          left-guard-left-error-impossible
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U = U} {e = e} eq
          }
    ; right-error-impossible = right-error-impossible simulation
    }

right-guard-forward-return :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  ∀ {n U V} →
  left n ≡ returned U V →
  Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U′ →
          Data.Product.Σ Value
            (λ V′ →
              Data.Product.Σ (WorldRelation U U′)
                (λ S →
                  WorldExtension R S ×
                  guard W′ right m ≡ returned U′ V′ ×
                  value-result S V V′))))
right-guard-forward-return simulation eq
    with forward-return simulation eq
right-guard-forward-return simulation eq
    | m , U′ , V′ , S , R≤S , right-eq , V~V′ =
  suc m , U′ , V′ , S , R≤S , right-eq , V~V′

right-guard-backward-return :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  ∀ {n U′ V′} →
  guard W′ right n ≡ returned U′ V′ →
  (Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U →
          Data.Product.Σ Value
            (λ V →
              Data.Product.Σ (WorldRelation U U′)
                (λ S →
                  WorldExtension R S ×
                  left m ≡ returned U V ×
                  value-result S V V′)))))
  ⊎
  (Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U → left m ≡ blamed U)))
right-guard-backward-return simulation {n = zero} ()
right-guard-backward-return simulation {n = suc n} eq =
  backward-return simulation eq

right-guard-target-blame :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  ∀ {n U′} →
  guard W′ right n ≡ blamed U′ →
  Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U → left m ≡ blamed U))
right-guard-target-blame simulation {n = zero} ()
right-guard-target-blame simulation {n = suc n} eq =
  target-blame-reflects simulation eq

right-guard-right-error-impossible :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  ∀ {n U′ e} →
  guard W′ right n ≡ failed U′ e →
  ⊥
right-guard-right-error-impossible simulation {n = zero} ()
right-guard-right-error-impossible simulation {n = suc n} eq =
  right-error-impossible simulation eq

right-guard-simulation :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  TerminalSimulation value-result R left (guard W′ right)
right-guard-simulation
    {W} {W′} {value-result} {R} {left} {right}
    simulation =
  record
    { left-stable = left-stable simulation
    ; right-stable =
        λ { {n} {o} terminal eq k →
          guard-terminal-stable
            {W = W′} {computation = right}
            (right-stable simulation)
            {n = n} {o = o} terminal eq k
          }
    ; forward-return =
        λ { {n} {U} {V} eq →
          right-guard-forward-return
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U = U} {V = V} eq
          }
    ; backward-return =
        λ { {n} {U′} {V′} eq →
          right-guard-backward-return
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U′ = U′} {V′ = V′} eq
          }
    ; target-blame-reflects =
        λ { {n} {U′} eq →
          right-guard-target-blame
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U′ = U′} eq
          }
    ; left-error-impossible = left-error-impossible simulation
    ; right-error-impossible =
        λ { {n} {U′} {e} eq →
          right-guard-right-error-impossible
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U′ = U′} {e = e} eq
          }
    }
