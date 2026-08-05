module InterpreterAdequacy.proof.NuTraceDecomposition where

-- File Charter:
--   * Decomposes a terminating `ν` trace into operand evaluation and the
--     allocation/instantiation tail.
--   * Keeps the adjusted allocation type and reveal coercion explicit after
--     every store change made while evaluating the operand.
--   * Uses only blame irreducibility outside the structural decomposition.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
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

record NuTraceDecomposition
    (A : Ty) (L : N.Term) (c : C.Coercion)
    (changes : StoreChanges) (result : N.Term) : Set where
  constructor nu-trace-decomposition
  field
    operand-changes : StoreChanges
    active-changes : StoreChanges
    operand-value : N.Term
    operand-is-value : N.Value operand-value
    operand-no-bullet : N.No• operand-value
    operand-trace : L —↠[ operand-changes ] operand-value
    active-trace :
      N.ν (applyTys operand-changes A) operand-value
        (applyCoercionUnderTyBinders operand-changes c)
        —↠[ active-changes ] result
    changes-eq : changes ≡ operand-changes ++ active-changes

open NuTraceDecomposition public

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
  ∀ {change changes A L L′ c result} →
  L —→[ change ] L′ →
  NuTraceDecomposition
    (applyTy change A) L′ (applyCoercionUnderTyBinder change c)
    changes result →
  NuTraceDecomposition A L c (change ∷ changes) result
prepend-operand-step L→L′
    (nu-trace-decomposition
      changes-L changes-A V vV no-V L′↠V active refl) =
  nu-trace-decomposition
    (_ ∷ changes-L) changes-A V vV no-V
    (↠-step L→L′ L′↠V) active refl

decompose-nu-value-trace :
  ∀ {A L c changes result} →
  N.ν A L c —↠[ changes ] result →
  N.Value result →
  NuTraceDecomposition A L c changes result
decompose-nu-value-trace ↠-refl ()
decompose-nu-value-trace
    (↠-step (ν-step vV no-V) tail) vR =
  nu-trace-decomposition [] (_ ∷ _) _ vV no-V ↠-refl
    (↠-step (ν-step vV no-V) tail) refl
decompose-nu-value-trace
    (↠-step blame-ν tail) vR =
  ⊥-elim (blame-does-not-reach-value tail vR)
decompose-nu-value-trace
    (↠-step (ξ-ν L→L′) tail) vR =
  prepend-operand-step L→L′
    (decompose-nu-value-trace tail vR)

nu-value-tail :
  ∀ {A u c changes v} →
  N.Value u →
  N.No• u →
  N.ν A u c —↠[ changes ] v →
  N.Value v →
  Σ[ tail ∈ StoreChanges ]
    (changes ≡ bind A ∷ tail) ×
    (((N.⇑ᵗᵐ u) N.•) N.⟨ c ⟩ —↠[ tail ] v)
nu-value-tail vu no-u ↠-refl ()
nu-value-tail vu no-u (↠-step root tail) vV
    with step-deterministic root (ν-step vu no-u)
nu-value-tail vu no-u (↠-step root tail) vV | refl , refl =
  _ , refl , tail
