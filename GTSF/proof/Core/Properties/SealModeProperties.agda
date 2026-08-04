module proof.Core.Properties.SealModeProperties where

-- File Charter:
--   * Defines small canonical seal-mode witnesses independent of cast
--     imprecision and narrowing/widening metatheory.
--   * Keeps store-mode facts out of high-fanout cast-property dependencies.

open import Coercions using (tag-or-idᵈ)
open import TermTyping using (SealModeStore★)


seal★-tag-or-id :
  ∀ {Σ} →
  SealModeStore★ tag-or-idᵈ Σ
seal★-tag-or-id α ()
