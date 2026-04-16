module All where

-- File Charter:
--   * Aggregate driver for extrinsic-inst PolyUpDown.
--   * Imports all modules in dependency order so checking this file validates
--   * the full extrinsic-inst development.

open import Types
open import TypeProperties
open import Imprecision
-- The following are under construction and not stable
--open import CastFactorization
--open import ImprecisionBridge
--open import ImprecisionCompleteness
open import Store
open import Ctx
open import UpDown
open import UpDownNorm
open import Terms
open import TermProperties
open import TypeCheckDec
open import Reduction
open import Progress
open import Preservation
open import Eval
open import Examples
open import LogicalRelation
open import Parametricity
