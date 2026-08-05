module InterpreterAdequacy.proof.CastBlameTraceDecomposition where

-- File Charter:
--   * Decomposes a cast trace ending in blame into operand blame or active
--     coercion blame.
--   * Records the final propagation step and coercion renaming caused by the
--     operand trace.
--   * Uses only the official small-step relation and blame irreducibility.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_)

import Coercions as C
open import NuReduction
import NuTerms as N
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)
open import proof.DGG.Core.NuReductionDeterminism using
  (blame-irreducible)

data CastBlameTraceDecomposition
    (M : N.Term) (c : C.Coercion) (changes : StoreChanges) : Set where
  operand-blames :
    ∀ {changes-M} →
    M —↠[ changes-M ] N.blame →
    changes ≡ changes-M ++ (keep ∷ []) →
    CastBlameTraceDecomposition M c changes

  active-blames :
    ∀ {changes-M changes-C u} →
    (vu : N.Value u) →
    M —↠[ changes-M ] u →
    (u N.⟨ applyCoercions changes-M c ⟩)
      —↠[ changes-C ] N.blame →
    changes ≡ changes-M ++ changes-C →
    CastBlameTraceDecomposition M c changes

private
  blame-trace-refl :
    ∀ {changes} →
    N.blame —↠[ changes ] N.blame →
    changes ≡ []
  blame-trace-refl ↠-refl = refl
  blame-trace-refl (↠-step blame→L L↠blame) =
    ⊥-elim (blame-irreducible blame→L)

prepend-operand-step :
  ∀ {change changes M M′ c} →
  M —→[ change ] M′ →
  CastBlameTraceDecomposition
    M′ (applyCoercion change c) changes →
  CastBlameTraceDecomposition M c (change ∷ changes)
prepend-operand-step M→M′ (operand-blames M′↠blame refl) =
  operand-blames (↠-step M→M′ M′↠blame) refl
prepend-operand-step M→M′
    (active-blames vu M′↠u active refl) =
  active-blames vu (↠-step M→M′ M′↠u) active refl

decompose-cast-blame-trace :
  ∀ {M c changes} →
  (M N.⟨ c ⟩) —↠[ changes ] N.blame →
  CastBlameTraceDecomposition M c changes
decompose-cast-blame-trace
    (↠-step (pure-step (β-id vV)) tail) =
  active-blames vV ↠-refl
    (↠-step (pure-step (β-id vV)) tail) refl
decompose-cast-blame-trace
    (↠-step (pure-step (β-seq vV)) tail) =
  active-blames vV ↠-refl
    (↠-step (pure-step (β-seq vV)) tail) refl
decompose-cast-blame-trace
    (↠-step (pure-step (β-inst vV)) tail) =
  active-blames vV ↠-refl
    (↠-step (pure-step (β-inst vV)) tail) refl
decompose-cast-blame-trace
    (↠-step (pure-step
      (tag-untag-ok {V = V} {G = G} vV)) tail) =
  active-blames (vV N.⟨ G C.! ⟩) ↠-refl
    (↠-step (pure-step (tag-untag-ok vV)) tail) refl
decompose-cast-blame-trace
    (↠-step (pure-step
      (tag-untag-bad {V = V} {G = G} {H = H} vV G≢H)) tail) =
  active-blames (vV N.⟨ G C.! ⟩) ↠-refl
    (↠-step (pure-step (tag-untag-bad vV G≢H)) tail) refl
decompose-cast-blame-trace
    (↠-step (pure-step
      (seal-unseal {α = α} {V = V} {A = A} {B = B} vV)) tail) =
  active-blames (vV N.⟨ C.seal A α ⟩) ↠-refl
    (↠-step (pure-step (seal-unseal vV)) tail) refl
decompose-cast-blame-trace
    (↠-step (pure-step blame-⟨⟩) tail)
    with blame-trace-refl tail
decompose-cast-blame-trace
    (↠-step (pure-step blame-⟨⟩) tail) | refl =
  operand-blames ↠-refl refl
decompose-cast-blame-trace
    (↠-step (ξ-⟨⟩ M→M′) tail) =
  prepend-operand-step M→M′ (decompose-cast-blame-trace tail)
