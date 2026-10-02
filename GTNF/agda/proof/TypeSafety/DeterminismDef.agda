module proof.TypeSafety.DeterminismDef where

-- File Charter:
--   * Gives the dashboard-facing name for the public determinism statement.
--   * Contains no determinism proof.

open import TypeSafety using (Determinism)

Determinism-Statement : Set
Determinism-Statement = Determinism
