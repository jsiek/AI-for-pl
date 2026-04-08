{-# OPTIONS --cumulativity --omega-in-omega #-}
module extrinsic.All where

-- Aggregate driver module:
-- importing this file should force Agda to check the entire extrinsic stack.

open import extrinsic.Types
open import extrinsic.Ctx
open import extrinsic.TypeSubst
open import extrinsic.Terms
open import extrinsic.TypeTermSubst
open import extrinsic.TermSubst
open import extrinsic.Reduction
open import extrinsic.Progress
open import extrinsic.Preservation
open import extrinsic.TypeSafety
open import extrinsic.Eval
open import extrinsic.Examples
open import extrinsic.ProductOmega
open import extrinsic.LogicalRelation
open import extrinsic.Parametricity
open import extrinsic.FreeTheorems
open import extrinsic.SystemF
