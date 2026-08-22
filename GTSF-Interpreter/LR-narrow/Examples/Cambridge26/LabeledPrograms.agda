module LR-narrow.Examples.Cambridge26.LabeledPrograms where

-- File Charter:
--   * Checks the four unnumbered Cambridge26 programs (a)--(d).
--   * Expands source type application with the interpreter's `ν` form.

open import LR-narrow.Examples.Cambridge26.Common
open import LR-narrow.Examples.Cambridge26.Specification
open import NuTerms using (_·_)
open import TypeCheck using (is-just)
open import Types using (★)

program-a : CheckedProgram
program-a = checked-programᵐ Nat (id-at Nat · nat 0) is-just

program-b : CheckedProgram
program-b = checked-programᵐ Nat
  (instantiate-at IdBody Nat (generalize-id id★) · nat 0) is-just

program-c : CheckedProgram
program-c = checked-programᵐ Nat
  (instantiate-at IdBody Nat (generalize-id j) · nat 0) is-just

program-d : CheckedProgram
program-d = checked-programᵐ ★
  (instantiate-id-dynamically (generalize-id id★) · nat★ 0) is-just
