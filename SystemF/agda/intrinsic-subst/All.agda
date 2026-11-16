module intrinsic-subst.All where

-- File Charter:
--   * Aggregate driver for the intrinsically typed System F development
--     built on the kit library (Subst/).
--   * Imports all modules so one check of this file validates the folder.

open import intrinsic-subst.Types
open import intrinsic-subst.TypeSubst
open import intrinsic-subst.Ctx
open import intrinsic-subst.Terms
open import intrinsic-subst.Reduction
open import intrinsic-subst.Examples
open import intrinsic-subst.Parametricity
open import intrinsic-subst.FreeTheorems
open import intrinsic-subst.MetaTheory
open import intrinsic-subst.proof.TypeSubst
open import intrinsic-subst.proof.TermSubst
open import intrinsic-subst.proof.Parametricity
open import intrinsic-subst.proof.FreeTheorems
