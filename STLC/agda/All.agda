module All where

-- File Charter:
--   * Aggregate driver for the STLC Agda development.
--   * Imports all main modules so one check of this file validates the folder.
--   * Keeps dependency order explicit for quick sanity checks.

open import STLC
open import Subst
open import TypeSafety
open import Eval
open import TypeCheckDec
open import Termination
open import Examples
