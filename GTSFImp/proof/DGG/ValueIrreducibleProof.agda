module proof.DGG.ValueIrreducibleProof where

-- File Charter:
--   * Provides the DGG-layer inhabitant of the value irreducibility surface.
--   * Reuses the completed reduction-theory proof directly.
--   * Exports value-irreducible* for DynamicGradualGuaranteeProof.

open import proof.Reduction.ValueIrreducibleDef
  using (ValueIrreducible*ᵀ)
import proof.Reduction.ValueIrreducibleProof as Reduction


value-irreducible* : ValueIrreducible*ᵀ
value-irreducible* = Reduction.value-irreducible*
