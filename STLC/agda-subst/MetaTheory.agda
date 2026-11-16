module MetaTheory where

-- File Charter:
--   * Public metatheory statements/wrappers for STLC.
--   * Combines type-safety and termination wrappers in one trust-facing module.

open import Agda.Builtin.List using ([])
open import Data.Product using (∃; ∃-syntax; _×_)
open import Data.Sum using (_⊎_)
open import STLC

import proof.TypeSafety as TypeSafetyProof
import proof.Termination as TerminationProof

preservation :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —→ N ->
  [] ⊢ N ⦂ A
preservation = TypeSafetyProof.preservation

progress :
  {M : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  (∃[ N ] (M —→ N)) ⊎ Value M
progress = TypeSafetyProof.progress_top

type-safety :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —↠ N ->
  (∃[ N′ ] (N —→ N′)) ⊎ Value N
type-safety = TypeSafetyProof.typeSafety

termination :
  {M : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  ∃[ V ] (M —↠ V) × Value V
termination = TerminationProof.termination
