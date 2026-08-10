module FunExt where

-- File Charter:
--   * Centralizes the sole function-extensionality assumption for GTSFImp.
--   * Exports `funext` for proof infrastructure that compares environments
--     and predicates extensionally.
--   * Depends only on the standard library's propositional extensionality
--     interface.

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Level using (0ℓ)

postulate
  funext : Extensionality 0ℓ 0ℓ
