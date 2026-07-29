module proof.InterpreterCoercionNarrowingProof where

-- File Charter:
--   * Provides inversion facts for the interpreter coercion leaves.
--   * Exposes the type narrowing carried by ground and tagged boundaries.
--   * Uses no operational semantics.

open import InterpreterCoercionNarrowing
open import Types

ground-narrowing-type :
  ∀ {G H} {gG : Ground G} {gH : Ground H} →
  InterpreterGroundNarrowing gG gH →
  InterpreterTypeNarrowing G H
ground-narrowing-type (ground-narrowing G~H) =
  G~H

left-tagged-boundary-type :
  ∀ {G} {gG : Ground G} →
  LeftTaggedBoundary gG →
  InterpreterTypeNarrowing G ★
left-tagged-boundary-type boundary =
  boundary

right-tagged-boundary-type :
  ∀ {G} {gG : Ground G} →
  RightTaggedBoundary gG →
  InterpreterTypeNarrowing ★ G
right-tagged-boundary-type boundary =
  boundary
