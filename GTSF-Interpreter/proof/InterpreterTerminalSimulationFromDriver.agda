module proof.InterpreterTerminalSimulationFromDriver where

-- File Charter:
--   * Closes a complete directional driver at the empty compiler runtime.
--   * Assembles one constructive terminal simulation for compiled endpoints.
--   * Uses direct interpreter stability and semantic error freedom only.
--   * Contains no interpreter recursion, reduction, catch-up, or DGG theorem.

open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (proj₁)
import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Compile using (compileᵀ)
open import Narrowing.CompileInterpreterNarrowing using
  (compile-preserves-interpreter-narrowing)
open import Ctx using (ctxWf-[])
import GradualTermImprecision as GTI
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Directional.InterpreterDirectionalDriverBundle
open import Typing.InterpreterErrorFreedom using
  (compiled-source-never-fails; compiled-target-never-fails)
open import Narrowing.InterpreterFramedValueNarrowing using
  (FramedValueResult; []⊑[]ᶠ)
open import Narrowing.InterpreterFramedValueNarrowingProperties using
  (framed-result-erases)
open import Core.InterpreterFuel using (interpret-terminal-stable)
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext using
  (empty-environment-realization; empty-runtime-narrowing)
open import Simulation.Core.InterpreterSimulationResult using
  (TerminalSimulation; TerminalStable)
open import Narrowing.InterpreterTermNarrowing
import NuTerms as N
open import proof.InterpreterDirectionalTransport using
  (backward-result-map; forward-result-map)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  (assumption-membership-unique-empty)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds
open Narrowing.InterpreterTermNarrowing.InterpreterValues


run-terminal-stable :
  ∀ M →
  TerminalStable (run M)
run-terminal-stable M {n} {o} terminal result-eq k =
  interpret-terminal-stable
    {W = emptyWorld} {γ = []} {θ = []} {M = M}
    {n = n} {o = o} terminal result-eq k


closed-terminal-simulation-from-driver :
  (∀ index → DirectionalDriverBundle index) →
  ∀ {M M′ A B}
    {p : [] ∣ zero ⊢ A ⊑ B ⊣ zero} →
  (M⊑M′ : [] ∣ zero ∣ zero ∣ []
    ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  let
    M⊢ = GTI.gradual-term-imprecision-source-typing M⊑M′
    M′⊢ = GTI.gradual-term-imprecision-target-typing M⊑M′
    N = proj₁ (compileᵀ ctxWf-[] M⊢)
    N′ = proj₁ (compileᵀ ctxWf-[] M′⊢)
  in
  TerminalSimulation ValueNarrowing empty-world⊑
    (run N) (run N′)
closed-terminal-simulation-from-driver
    bundles {A = A} {B = B} {p = p} M⊑M′ =
  record
    { left-stable =
        λ { {n} {o} terminal result-eq k →
          run-terminal-stable N {n = n} {o = o}
            terminal result-eq k }
    ; right-stable =
        λ { {n} {o} terminal result-eq k →
          run-terminal-stable N′ {n = n} {o = o}
            terminal result-eq k }
    ; forward-return = λ { {n} result-eq → forward n result-eq }
    ; backward-return = λ { {n} result-eq → backward n result-eq }
    ; target-blame-reflects = λ { {n} result-eq → blame n result-eq }
    ; left-error-impossible =
        λ { {n} {U} {e} result-eq →
          source-error-free {index = n} {U = U} {e = e} result-eq }
    ; right-error-impossible =
        λ { {n} {U′} {e} result-eq →
          target-error-free {index = n} {U′ = U′} {e = e} result-eq }
    }
  where
  M⊢ = GTI.gradual-term-imprecision-source-typing M⊑M′
  M′⊢ = GTI.gradual-term-imprecision-target-typing M⊑M′
  N = proj₁ (compileᵀ ctxWf-[] M⊢)
  N′ = proj₁ (compileᵀ ctxWf-[] M′⊢)

  terms :
    OpenInterpreterTermNarrowing empty-world⊑
      [] zero zero [] [] N N′ A B p
  terms =
    compile-preserves-interpreter-narrowing
      ctxWf-[] ctxWf-[] M⊑M′

  forward :
    ∀ index →
    ForwardReturnSimulation ValueNarrowing empty-world⊑
      (run N) (run N′) index
  forward index =
    forward-result-map
      {left-index = index}
      {source-result = FramedValueResult [] [] [] p}
      {target-result = ValueNarrowing}
      {R = empty-world⊑}
      {left = run N} {right = run N′}
      (term-forward (bundles index)
        assumption-membership-unique-empty
        empty-runtime-narrowing
        empty-environment-realization
        []⊑[]ᶠ terms)
      (λ R≤S result → framed-result-erases result)

  backward :
    ∀ index →
    BackwardReturnSimulation ValueNarrowing empty-world⊑
      (run N) (run N′) index
  backward index =
    backward-result-map
      {right-index = index}
      {source-result = FramedValueResult [] [] [] p}
      {target-result = ValueNarrowing}
      {R = empty-world⊑}
      {left = run N} {right = run N′}
      (term-backward (bundles index)
        assumption-membership-unique-empty
        empty-runtime-narrowing
        empty-environment-realization
        []⊑[]ᶠ terms)
      (λ R≤S result → framed-result-erases result)

  blame :
    ∀ index →
    TargetBlameSimulation empty-world⊑
      (run N) (run N′) index
  blame index =
    term-target-blame (bundles index)
      assumption-membership-unique-empty
      empty-runtime-narrowing
      empty-environment-realization
      []⊑[]ᶠ terms

  source-error-free :
    ∀ {index U e} →
    run N index ≡ failed U e →
    Data.Empty.⊥
  source-error-free {index} {U} {e} result-eq =
    compiled-source-never-fails M⊑M′ index U e result-eq

  target-error-free :
    ∀ {index U′ e} →
    run N′ index ≡ failed U′ e →
    Data.Empty.⊥
  target-error-free {index} {U′} {e} result-eq =
    compiled-target-never-fails M⊑M′ index U′ e result-eq
