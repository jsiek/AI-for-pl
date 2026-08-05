module Simulation.Core.InterpreterTerminalSimulation where

-- File Charter:
--   * Public closed-program terminal simulation assembled from the driver.
--   * States the compiler-facing theorem explicitly at its use boundary.
--   * Delegates the reduction-free closure proof to a private module.

open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (proj₁)

open import Compile using (compileᵀ)
open import Ctx using (ctxWf-[])
import GradualTermImprecision as GTI
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter using (run)
open import Simulation.Directional.InterpreterDirectionalDriverBundle using
  (DirectionalDriverBundle)
open import Simulation.Core.InterpreterSimulationResult using
  (TerminalSimulation)
open import Narrowing.InterpreterTermNarrowing
import proof.InterpreterTerminalSimulationFromDriver as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.InterpreterValues


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
  TerminalSimulation ValueNarrowing
    Narrowing.InterpreterTermNarrowing.RelatedWorlds.empty-world⊑
    (run N) (run N′)
closed-terminal-simulation-from-driver =
  Proof.closed-terminal-simulation-from-driver
