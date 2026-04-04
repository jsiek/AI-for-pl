module Safety where

open import Agda.Builtin.List using ([])

open import STLC
open import TypeSafety using (ProgressResult; progress_top; preservation)

------------------------------------------------------------------------
-- Closed-term safety wrapper
------------------------------------------------------------------------

record Safety (M : Term) (A : Ty) : Set where
  constructor safety
  field
    progress-witness : ProgressResult M
    step-preservation : ∀ {N : Term} -> M —→ N -> HasType [] N A

open Safety public

typeSafety :
  {M : Term} {A : Ty} ->
  HasType [] M A ->
  Safety M A
typeSafety hM = safety (progress_top hM) (preservation hM)

typeSafety-step :
  {M : Term} {A : Ty} ->
  HasType [] M A ->
  ∀ {N : Term} -> M —→ N -> HasType [] N A
typeSafety-step hM s = preservation hM s

typeSafety-↠ :
  {M N : Term} {A : Ty} ->
  HasType [] M A ->
  M —↠ N ->
  HasType [] N A
typeSafety-↠ hM (ms-refl _) = hM
typeSafety-↠ hM (ms-step _ s ms) = typeSafety-↠ (preservation hM s) ms
