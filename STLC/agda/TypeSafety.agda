module TypeSafety where

-- File Charter:
--   * Public statements for progress/preservation and type safety.
--   * Proof terms live in proof/TypeSafety.agda.

open import Agda.Builtin.List using ([])
open import Agda.Builtin.Sigma using (Σ)
open import Data.Sum using (_⊎_)
open import STLC

import proof.TypeSafety as Proof

preservation :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —→ N ->
  [] ⊢ N ⦂ A
preservation = Proof.preservation

progress_top :
  {M : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  (Σ Term (λ N -> M —→ N)) ⊎ Value M
progress_top = Proof.progress_top

progress :
  {M : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  (Σ Term (λ N -> M —→ N)) ⊎ Value M
progress = progress_top

typeSafety :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —↠ N ->
  (Σ Term (λ N' -> N —→ N')) ⊎ Value N
typeSafety = Proof.typeSafety

type-safety :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —↠ N ->
  (Σ Term (λ N' -> N —→ N')) ⊎ Value N
type-safety = typeSafety
