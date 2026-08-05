module InterpreterAdequacy.proof.NuBlameTraceDecomposition where

-- File Charter:
--   * Decomposes a `ν` trace ending in blame into operand blame or blame in
--     the allocation/instantiation/coercion tail.
--   * Tracks the allocation type and reveal coercion through store changes.
--   * Uses only the official small-step relation and blame irreducibility.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_; Σ-syntax)

import Coercions as C
open import NuReduction
import NuTerms as N
open import Types using (Ty)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercionUnderTyBinders)
open import proof.DGG.Core.NuReductionDeterminism using
  (blame-irreducible; step-deterministic)

data NuBlameTraceDecomposition
    (A : Ty) (L : N.Term) (c : C.Coercion)
    (changes : StoreChanges) : Set where
  operand-blames :
    ∀ {changes-L} →
    L —↠[ changes-L ] N.blame →
    changes ≡ changes-L ++ (keep ∷ []) →
    NuBlameTraceDecomposition A L c changes

  active-blames :
    ∀ {changes-L changes-A f} →
    (vf : N.Value f) →
    (no-f : N.No• f) →
    L —↠[ changes-L ] f →
    N.ν (applyTys changes-L A) f
      (applyCoercionUnderTyBinders changes-L c)
      —↠[ changes-A ] N.blame →
    changes ≡ changes-L ++ changes-A →
    NuBlameTraceDecomposition A L c changes

private
  blame-trace-refl :
    ∀ {changes} →
    N.blame —↠[ changes ] N.blame →
    changes ≡ []
  blame-trace-refl ↠-refl = refl
  blame-trace-refl (↠-step blame→L L↠blame) =
    ⊥-elim (blame-irreducible blame→L)

prepend-operand-step :
  ∀ {change changes A L L′ c} →
  L —→[ change ] L′ →
  NuBlameTraceDecomposition
    (applyTy change A) L′ (applyCoercionUnderTyBinder change c)
    changes →
  NuBlameTraceDecomposition A L c (change ∷ changes)
prepend-operand-step L→L′ (operand-blames L′↠blame refl) =
  operand-blames (↠-step L→L′ L′↠blame) refl
prepend-operand-step L→L′
    (active-blames vf no-f L′↠f active refl) =
  active-blames vf no-f (↠-step L→L′ L′↠f) active refl

decompose-nu-blame-trace :
  ∀ {A L c changes} →
  N.ν A L c —↠[ changes ] N.blame →
  NuBlameTraceDecomposition A L c changes
decompose-nu-blame-trace
    (↠-step (ν-step vV no-V) tail) =
  active-blames vV no-V ↠-refl
    (↠-step (ν-step vV no-V) tail) refl
decompose-nu-blame-trace
    (↠-step blame-ν tail)
    with blame-trace-refl tail
decompose-nu-blame-trace
    (↠-step blame-ν tail) | refl =
  operand-blames ↠-refl refl
decompose-nu-blame-trace
    (↠-step (ξ-ν L→L′) tail) =
  prepend-operand-step L→L′ (decompose-nu-blame-trace tail)

nu-blame-tail :
  ∀ {A u c changes} →
  N.Value u →
  N.No• u →
  N.ν A u c —↠[ changes ] N.blame →
  Σ[ tail ∈ StoreChanges ]
    (changes ≡ bind A ∷ tail) ×
    (((N.⇑ᵗᵐ u) N.•) N.⟨ c ⟩ —↠[ tail ] N.blame)
nu-blame-tail vu no-u (↠-step root tail)
    with step-deterministic root (ν-step vu no-u)
nu-blame-tail vu no-u (↠-step root tail) | refl , refl =
  _ , refl , tail
