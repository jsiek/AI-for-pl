module InterpreterAdequacy.proof.CastTraceDecomposition where

-- File Charter:
--   * Decomposes a terminating cast trace into operand evaluation and active
--     cast phases.
--   * Treats an inert cast on an already evaluated operand as an empty active
--     phase and records coercion renaming across allocation steps.
--   * Uses only reduction determinism and value irreducibility.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)

import Coercions as C
open import NuReduction
import NuTerms as N
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)
open import proof.DGG.Core.NuReductionDeterminism using
  (blame-irreducible)

record CastTraceDecomposition
    (M : N.Term) (c : C.Coercion) (changes : StoreChanges)
    (result : N.Term) : Set where
  constructor cast-trace-decomposition
  field
    operand-changes : StoreChanges
    active-changes : StoreChanges
    operand-value : N.Term
    operand-is-value : N.Value operand-value
    operand-trace : M —↠[ operand-changes ] operand-value
    active-trace :
      (operand-value N.⟨ applyCoercions operand-changes c ⟩)
        —↠[ active-changes ] result
    changes-eq : changes ≡ operand-changes ++ active-changes

open CastTraceDecomposition public

private
  blame-does-not-reach-value :
    ∀ {changes V} →
    N.blame —↠[ changes ] V →
    N.Value V →
    ⊥
  blame-does-not-reach-value ↠-refl ()
  blame-does-not-reach-value (↠-step blame→L L↠V) vV =
    ⊥-elim (blame-irreducible blame→L)

prepend-operand-step :
  ∀ {change changes M M′ c result} →
  M —→[ change ] M′ →
  CastTraceDecomposition
    M′ (applyCoercion change c) changes result →
  CastTraceDecomposition M c (change ∷ changes) result
prepend-operand-step M→M′
    (cast-trace-decomposition
      changes-M changes-A V vV M′↠V active refl) =
  cast-trace-decomposition
    (_ ∷ changes-M) changes-A V vV
    (↠-step M→M′ M′↠V) active refl

decompose-cast-value-trace :
  ∀ {M c changes result} →
  (M N.⟨ c ⟩) —↠[ changes ] result →
  N.Value result →
  CastTraceDecomposition M c changes result
decompose-cast-value-trace ↠-refl (vM N.⟨ inert ⟩) =
  cast-trace-decomposition [] [] _ vM ↠-refl ↠-refl refl
decompose-cast-value-trace
    (↠-step (pure-step (β-id vV)) tail) vR =
  cast-trace-decomposition [] (keep ∷ _) _ vV ↠-refl
    (↠-step (pure-step (β-id vV)) tail) refl
decompose-cast-value-trace
    (↠-step (pure-step (β-seq vV)) tail) vR =
  cast-trace-decomposition [] (keep ∷ _) _ vV ↠-refl
    (↠-step (pure-step (β-seq vV)) tail) refl
decompose-cast-value-trace
    (↠-step (pure-step (β-inst vV)) tail) vR =
  cast-trace-decomposition [] (keep ∷ _) _ vV ↠-refl
    (↠-step (pure-step (β-inst vV)) tail) refl
decompose-cast-value-trace
    (↠-step (pure-step
      (tag-untag-ok {V = V} {G = G} vV)) tail) vR =
  cast-trace-decomposition [] (keep ∷ _) (V N.⟨ G C.! ⟩)
    (vV N.⟨ G C.! ⟩)
    ↠-refl (↠-step (pure-step (tag-untag-ok vV)) tail) refl
decompose-cast-value-trace
    (↠-step (pure-step (tag-untag-bad vV G≢H)) tail) vR =
  ⊥-elim (blame-does-not-reach-value tail vR)
decompose-cast-value-trace
    {M = V N.⟨ C.seal A X ⟩} {c = C.unseal .X B}
    (↠-step (pure-step (seal-unseal vV)) tail) vR =
  cast-trace-decomposition [] (keep ∷ _) (V N.⟨ C.seal A X ⟩)
    (vV N.⟨ C.seal A X ⟩) ↠-refl
    (↠-step (pure-step (seal-unseal vV)) tail) refl
decompose-cast-value-trace
    (↠-step (pure-step blame-⟨⟩) tail) vR =
  ⊥-elim (blame-does-not-reach-value tail vR)
decompose-cast-value-trace
    (↠-step (ξ-⟨⟩ M→M′) tail) vR =
  prepend-operand-step M→M′
    (decompose-cast-value-trace tail vR)
