module strong.All where

-- Aggregate driver for Strong System F: type-checking this module
-- type-checks the whole development.

open import strong.Types
open import strong.TypeSubst
open import strong.Context
open import strong.Weakening
open import strong.Unfold
open import strong.Boundary
open import strong.BReduction
open import strong.ScopeBridge
open import strong.TermSubst
open import strong.DualDef
open import strong.BPreservation
open import strong.Canonical
open import strong.ProgressDef
open import strong.Progress
open import strong.Show
open import strong.EvalDec
open import strong.Eval
