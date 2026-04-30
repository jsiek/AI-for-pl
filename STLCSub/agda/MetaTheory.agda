module MetaTheory where

-- File Charter:
--   * Public metatheory statements/wrappers for STLCSub.
--   * Keeps the theorem surface explicit while delegating proof details to
--     `proof.TypeSafety`.

open import Agda.Builtin.List using ([])
open import Data.Product using (∃-syntax)
open import Data.Sum using (_⊎_)

open import STLCSub
import proof.TypeSafety as TypeSafetyProof

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
progress = TypeSafetyProof.progress

type-safety :
  {M N : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  M —↠ N ->
  (∃[ N′ ] (N —→ N′)) ⊎ Value N
type-safety = TypeSafetyProof.type-safety
