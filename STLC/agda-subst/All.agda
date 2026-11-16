module All where

-- File Charter:
--   * Aggregate driver for the STLC Agda development.
--   * Imports all main modules so one check of this file validates the folder.
--   * Keeps dependency order explicit for quick sanity checks.

-- The ordering of these files is deliberate.
-- One should define the language and test it before proving the metatheory.

open import STLC
open import Eval
open import TypeCheckDec
open import Examples
open import MetaTheory
