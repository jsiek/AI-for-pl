module proof.LR-narrow.FunExt where

-- File Charter:
--   * Localizes function extensionality to the interpreter LR proof.
--   * Keeps the upstream GTSFImp core free of postulates and safe-checkable.
--   * Supplies equality of finite consistency environments and predicates.

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Level using (0ℓ)

postulate
  funext : Extensionality 0ℓ 0ℓ
