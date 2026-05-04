module All where

-- File Charter:
--   * Aggregate driver for the current PolyConvert extrinsic-inst slice.
--   * Imports the copied type infrastructure plus indexed imprecision,
--     conversions, and the term/type-system front end.
--   * Metatheory and operational modules will be added explicitly as they mature.

open import Types
open import TypeProperties
open import Ctx
open import Store
open import Imprecision
open import Conversion
open import Terms
open import Reduction
open import MetaTheory
