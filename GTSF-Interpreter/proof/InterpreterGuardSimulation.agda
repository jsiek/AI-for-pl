module proof.InterpreterGuardSimulation where

-- File Charter:
--   * Adds or removes the outer constructor-fuel guard from a simulation.
--   * Preserves independently chosen terminal indices by shifting both
--     guarded observations up or down by one.
--   * Contains no syntax or reduction semantics.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Interpreter
open import Core.InterpreterOutcome
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.InterpreterValues
open ITN.RelatedWorlds

guard-terminal-stable :
  ∀ {W computation} →
  TerminalStable computation →
  TerminalStable (guard W computation)
guard-terminal-stable stable
    {n = zero} terminal eq k =
  ⊥-elim (timed-terminal-absurd eq terminal)
guard-terminal-stable stable
    {n = suc n} terminal eq k =
  stable terminal eq k

guard-forward-return :
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
                  guard W′ right m ≡ returned U′ V′ ×
                  value-result S V V′))))
guard-forward-return simulation {n = zero} ()
guard-forward-return simulation {n = suc n} eq
    with forward-return simulation eq
guard-forward-return simulation eq
    | m , U′ , V′ , S , R≤S , right-eq , V~V′ =
  suc m , U′ , V′ , S , R≤S , right-eq , V~V′

guard-backward-return :
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
                  guard W left m ≡ returned U V ×
                  value-result S V V′)))))
  ⊎
  (Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U → guard W left m ≡ blamed U)))
guard-backward-return simulation {n = zero} ()
guard-backward-return simulation {n = suc n} eq
    with backward-return simulation eq
guard-backward-return simulation eq
    | inj₁ (m , U , V , S , R≤S , left-eq , V~V′) =
  inj₁ (suc m , U , V , S , R≤S , left-eq , V~V′)
guard-backward-return simulation eq
    | inj₂ (m , U , left-eq) =
  inj₂ (suc m , U , left-eq)

guard-target-blame :
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
        (λ U → guard W left m ≡ blamed U))
guard-target-blame simulation {n = zero} ()
guard-target-blame simulation {n = suc n} eq
    with target-blame-reflects simulation eq
guard-target-blame simulation eq
    | m , U , left-eq =
  suc m , U , left-eq

guard-left-error-impossible :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  ∀ {n U e} →
  guard W left n ≡ failed U e →
  Data.Empty.⊥
guard-left-error-impossible simulation {n = zero} ()
guard-left-error-impossible simulation {n = suc n} eq =
  left-error-impossible simulation eq

guard-right-error-impossible :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  ∀ {n U′ e} →
  guard W′ right n ≡ failed U′ e →
  Data.Empty.⊥
guard-right-error-impossible simulation {n = zero} ()
guard-right-error-impossible simulation {n = suc n} eq =
  right-error-impossible simulation eq

guard-simulation :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  TerminalSimulation value-result R
    (guard W left) (guard W′ right)
guard-simulation
    {W} {W′} {value-result} {R} {left} {right} simulation =
  record
    { left-stable =
        λ { {n} {o} terminal eq k →
          guard-terminal-stable
            {W = W} {computation = left}
            (left-stable simulation)
            {n = n} {o = o} terminal eq k
          }
    ; right-stable =
        λ { {n} {o} terminal eq k →
          guard-terminal-stable
            {W = W′} {computation = right}
            (right-stable simulation)
            {n = n} {o = o} terminal eq k
          }
    ; forward-return =
        λ { {n} {U} {V} eq →
          guard-forward-return
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U = U} {V = V} eq
          }
    ; backward-return =
        λ { {n} {U′} {V′} eq →
          guard-backward-return
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U′ = U′} {V′ = V′} eq
          }
    ; target-blame-reflects =
        λ { {n} {U′} eq →
          guard-target-blame
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U′ = U′} eq
          }
    ; left-error-impossible =
        λ { {n} {U} {e} eq →
          guard-left-error-impossible
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U = U} {e = e} eq
          }
    ; right-error-impossible =
        λ { {n} {U′} {e} eq →
          guard-right-error-impossible
            {W = W} {W′ = W′}
            {value-result = value-result} {R = R}
            {left = left} {right = right}
            simulation {n = n} {U′ = U′} {e = e} eq
          }
    }

unguard-terminal-stable :
  ∀ {W computation} →
  TerminalStable (guard W computation) →
  TerminalStable computation
unguard-terminal-stable guarded-stable
    {n} {o} terminal eq k =
  guarded-stable
    {n = suc n} {o = o}
    terminal eq k

unguard-forward-return :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R
    (guard W left) (guard W′ right) →
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
                  right m ≡ returned U′ V′ ×
                  value-result S V V′))))
unguard-forward-return simulation {n} eq
    with forward-return simulation {n = suc n} eq
unguard-forward-return simulation eq
    | zero , U′ , V′ , S , R≤S , right-eq , V~V′ =
  ⊥-elim (timed≢returned right-eq)
unguard-forward-return simulation eq
    | suc m , U′ , V′ , S , R≤S , right-eq , V~V′ =
  m , U′ , V′ , S , R≤S , right-eq , V~V′

unguard-backward-return :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R
    (guard W left) (guard W′ right) →
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
                  left m ≡ returned U V ×
                  value-result S V V′)))))
  ⊎
  (Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U → left m ≡ blamed U)))
unguard-backward-return simulation {n} eq
    with backward-return simulation {n = suc n} eq
unguard-backward-return simulation eq
    | inj₁
        (zero , U , V , S , R≤S , left-eq , V~V′) =
  ⊥-elim (timed≢returned left-eq)
unguard-backward-return simulation eq
    | inj₁
        (suc m , U , V , S , R≤S , left-eq , V~V′) =
  inj₁ (m , U , V , S , R≤S , left-eq , V~V′)
unguard-backward-return simulation eq
    | inj₂ (zero , U , left-eq) =
  ⊥-elim (timed≢blamed left-eq)
unguard-backward-return simulation eq
    | inj₂ (suc m , U , left-eq) =
  inj₂ (m , U , left-eq)

unguard-target-blame :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R
    (guard W left) (guard W′ right) →
  ∀ {n U′} →
  right n ≡ blamed U′ →
  Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U → left m ≡ blamed U))
unguard-target-blame simulation {n} eq
    with target-blame-reflects simulation {n = suc n} eq
unguard-target-blame simulation eq
    | zero , U , left-eq =
  ⊥-elim (timed≢blamed left-eq)
unguard-target-blame simulation eq
    | suc m , U , left-eq =
  m , U , left-eq

unguard-simulation :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R
    (guard W left) (guard W′ right) →
  TerminalSimulation value-result R left right
unguard-simulation
    {W} {W′} {value-result} {R} {left} {right} guarded =
  record
    { left-stable =
        λ { {n} {o} terminal eq k →
          left-stable guarded
            {n = suc n} {o = o}
            terminal eq k
          }
    ; right-stable =
        λ { {n} {o} terminal eq k →
          right-stable guarded
            {n = suc n} {o = o}
            terminal eq k
          }
    ; forward-return =
        unguard-forward-return
          {W = W} {W′ = W′} {R = R}
          {left = left} {right = right}
          guarded
    ; backward-return =
        unguard-backward-return
          {W = W} {W′ = W′} {R = R}
          {left = left} {right = right}
          guarded
    ; target-blame-reflects =
        unguard-target-blame
          {W = W} {W′ = W′} {R = R}
          {left = left} {right = right}
          guarded
    ; left-error-impossible =
        λ { {n} {U} {e} eq →
          left-error-impossible guarded
            {n = suc n} {U = U} {e = e} eq
          }
    ; right-error-impossible =
        λ { {n} {U′} {e} eq →
          right-error-impossible guarded
            {n = suc n} {U′ = U′} {e = e} eq
          }
    }
