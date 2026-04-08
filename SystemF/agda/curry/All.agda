{-# OPTIONS --cumulativity --omega-in-omega #-}
module curry.All where

-- Aggregate driver module:
-- importing this file should force Agda to check the entire curry stack.

open import curry.Types
open import curry.TypeSubst
open import curry.Terms
open import curry.Reduction
open import curry.Progress
open import curry.Preservation
open import curry.TypeSafety
open import curry.Eval
open import curry.Examples
open import curry.ProductOmega
open import curry.LogicalRelation
open import curry.Parametricity
open import curry.FreeTheorems
open import curry.SystemF
