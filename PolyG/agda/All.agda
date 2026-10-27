module All where

-- File Charter:
--   * Aggregate driver for the public PolyG Agda development (PolyGν and
--     PolyCν of Max New's thesis, ∀ν fragment).
--   * Imports only the trust-facing modules; they import the proofs.

open import Types
open import Terms
open import Reduction
open import Typing
open import StoreWf
open import GradualTerms
open import Compile
open import TermPrecision
open import GradualTermPrecision
open import CompileInvariants
open import GradualityDefinitions
open import GraphModel
open import Denotation
open import DenotInvariants
open import TypeSafety
open import CompileMeta
open import DenotationMeta
open import MetaTheory
open import Eval
open import Examples
open import ExamplesCoverage
