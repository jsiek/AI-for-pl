module All where

-- File Charter:
--   * Aggregate driver for extrinsic PolyUpDown.
--   * Imports all modules in dependency order so a single check of this file
--   * verifies the whole extrinsic development.

open import Types
open import TypeProperties
open import Store
open import Ctx
open import UpDown
open import Terms
open import TermProperties
open import Reduction
open import Progress
open import Preservation
open import Eval
open import Examples
