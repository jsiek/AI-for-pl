module proof.InterpreterIndexedImmediateReturn where

-- File Charter:
--   * Builds an indexed terminal simulation when both computations return
--     related values at every positive index.
--   * Keeps the observed indices and the concrete one-step witnesses
--     explicit.
--   * Uses no evaluator recursion or reduction semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.RelatedWorlds

indexed-immediate-returns :
  ∀ {W W′ V V′ left-index right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  left (suc left-index) ≡ returned W V →
  right (suc right-index) ≡ returned W′ V′ →
  left (suc zero) ≡ returned W V →
  right (suc zero) ≡ returned W′ V′ →
  value-result R V V′ →
  IndexedTerminalSimulation value-result R left right
    (suc left-index) (suc right-index)
indexed-immediate-returns
    {W = W} {W′ = W′} {V = V} {V′ = V′}
    {value-result = value-result} {R = R}
    {left = left} {right = right}
    left-observed right-observed left-witness right-witness related =
  record
    { forward-return =
        λ eq → forward-result (trans (sym left-observed) eq)
    ; backward-return =
        λ eq → backward-result (trans (sym right-observed) eq)
    ; target-blame-reflects =
        λ eq → ⊥-elim (returned-not-blamed
          (trans (sym right-observed) eq))
    }
  where
  forward-result :
    ∀ {Z Q} →
    returned W V ≡ returned Z Q →
    Data.Product.Σ StepIndex λ m →
    Data.Product.Σ World λ Z′ →
    Data.Product.Σ Value λ Q′ →
    Data.Product.Σ (WorldRelation Z Z′) λ S →
      WorldExtension R S Data.Product.×
      right m ≡ returned Z′ Q′ Data.Product.×
      value-result S Q Q′
  forward-result refl =
    suc zero , W′ , V′ , R , extension-refl ,
    right-witness , related

  backward-result :
    ∀ {Z′ Q′} →
    returned W′ V′ ≡ returned Z′ Q′ →
    (Data.Product.Σ StepIndex λ m →
     Data.Product.Σ World λ Z →
     Data.Product.Σ Value λ Q →
     Data.Product.Σ (WorldRelation Z Z′) λ S →
       WorldExtension R S Data.Product.×
       left m ≡ returned Z Q Data.Product.×
       value-result S Q Q′)
    Data.Sum.⊎
    (Data.Product.Σ StepIndex λ m →
     Data.Product.Σ World λ Z →
       left m ≡ blamed Z)
  backward-result refl =
    inj₁
      (suc zero , W , V , R , extension-refl ,
       left-witness , related)

  returned-not-blamed :
    ∀ {Z} →
    returned W′ V′ ≡ blamed Z →
    Data.Empty.⊥
  returned-not-blamed ()
