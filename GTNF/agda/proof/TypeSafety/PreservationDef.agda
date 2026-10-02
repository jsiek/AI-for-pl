module proof.TypeSafety.PreservationDef where

-- File Charter:
--   * Gives dashboard-facing names for the public preservation statements.
--   * Contains no preservation proof.

open import TypeSafety using (Preservation; PreservationWf; Preservation*)

Preservation-Statement : Set
Preservation-Statement = Preservation

PreservationWf-Statement : Set
PreservationWf-Statement = PreservationWf

Preservation*-Statement : Set
Preservation*-Statement = Preservation*
