module All where

-- File Charter:
--   * Aggregate driver for extrinsic-inst PolyUpDown.
--   * Imports all modules in dependency order so checking this file validates
--   * the full extrinsic-inst development.

open import Types
open import TypeProperties
open import Imprecision
open import ImprecisionBridge
open import ImprecisionCompleteness
open import Store
open import Ctx
open import UpDown
open import Terms
open import TermPrecision
open import TermProperties
open import TypeCheckDec
open import Reduction

open import ReductionFresh
open import EvalPartialFresh
open import CoverageFresh
open import ExamplesFresh
open import ProgressFresh
open import PreservationFresh

open import Progress
open import Preservation
open import Eval
open import Examples

open import LogicalRelation
open import LogicalRelationAlt
-- UNDER CONSTRUCTION
--open import Parametricity
--open import DynamicGradualGuarantee
