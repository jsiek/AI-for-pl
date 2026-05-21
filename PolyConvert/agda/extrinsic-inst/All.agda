{-# OPTIONS --allow-unsolved-metas #-}
module All where

-- File Charter:
--   * Aggregate driver for the current PolyConvert extrinsic-inst slice.
--   * Imports the copied type infrastructure plus indexed imprecision,
--     conversions, and the term/type-system front end.
--   * Metatheory and operational modules are imported explicitly as they
--     mature.

open import Types
open import Ctx
open import Store
open import Imprecision
open import Conversion
open import Primitives
open import Terms
open import GradualTerms
open import GradualTermImprecision
open import Compile
open import TermImprecision
open import Reduction
open import TypeSafety
open import GradualGuarantee
