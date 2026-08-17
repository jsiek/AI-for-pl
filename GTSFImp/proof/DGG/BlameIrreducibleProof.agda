module proof.DGG.BlameIrreducibleProof where

-- File Charter:
--   * Provides the DGG-layer inhabitant of the blame irreducibility surface.
--   * Reuses the completed reduction-theory proof directly.
--   * Exports blame-irreducible* for DynamicGradualGuaranteeProof.

open import proof.Reduction.BlameIrreducibleDef
  using (BlameIrreducible*ᵀ)
import proof.Reduction.BlameIrreducibleProof as Reduction


blame-irreducible* : BlameIrreducible*ᵀ
blame-irreducible* = Reduction.blame-irreducible*
