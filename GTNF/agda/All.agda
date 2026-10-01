module All where

-- Aggregate driver for GTNF (GTNF/design.md): type-checking this module
-- type-checks the whole development.  The definitional layer is forked
-- from SystemF/agda/strong-rep-nu (System νF) and extended with ★,
-- coercions, casts and blame; there is no metatheory yet.

open import Types
open import proof.Types
open import Ctx
open import proof.Ctx
open import Lookup
open import Boundary
open import Conversion
open import Coercion
open import Terms
open import TermSubst
open import Reduction

-- executable, derivation-producing type checking, and the step function
open import TypeCheck
open import Eval

-- design.md §8's examples, run by `refl`
open import Examples

-- pairs of programs for designing the cast-term imprecision
-- type imprecision (GTSFImp's, design.md §12.1)
open import Imprecision

open import ImprecisionExamples

-- the term-imprecision examples of papers/cambridge26.lagda.md, run
open import CambridgeExamples

-- de Bruijn → named rendering (scripts/render_gtnf.sh)
open import Show
