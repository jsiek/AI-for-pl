module proof.TypeSafety.Determinism where

-- File Charter:
--   * Instantiates the GTNF determinism proof with irreducibility.

open import proof.TypeSafety.Irreducible using (irreducible)
import proof.TypeSafety.DeterminismProof as DeterminismProof

open DeterminismProof.Impl irreducible public
