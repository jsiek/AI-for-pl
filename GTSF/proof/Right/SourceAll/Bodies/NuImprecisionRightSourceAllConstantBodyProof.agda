module
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllConstantBodyProof
  where

-- File Charter:
--   * Proves that the constant-body source-universal closing case is
--     impossible by source typing and the non-vacuity occurrence premise.
--   * Contains no semantic catch-up, recursion, result/view/outcome type,
--     postulate, hole, permissive option, or broad simulation import.

open import Primitives using (κℕ)
open import QuotientedTermImprecision using
  (nu-term-imprecision-source-typing)
open import TermTyping using (⊢$)
open import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllConstantBodyDef
  using (WorldCoherentRightSourceAllConstantBodyᵀ)


world-coherent-right-source-all-constant-body-proofᵀ :
  WorldCoherentRightSourceAllConstantBodyᵀ
world-coherent-right-source-all-constant-body-proofᵀ
    {k = κℕ n} {occ = occ}
    prefix coherent exclusive unique wfR okN′
    liftρ liftγ rel
    with nu-term-imprecision-source-typing rel
world-coherent-right-source-all-constant-body-proofᵀ
    {k = κℕ n} {occ = ()}
    prefix coherent exclusive unique wfR okN′
    liftρ liftγ rel
    | ⊢$ .(κℕ n)
