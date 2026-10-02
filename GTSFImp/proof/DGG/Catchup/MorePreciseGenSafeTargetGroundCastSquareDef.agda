{-# OPTIONS --safe #-}

module proof.DGG.Catchup.MorePreciseGenSafeTargetGroundCastSquareDef where

-- File Charter:
--   * States the general consistency/imprecision induction exposed by the
--     paired target all/gen ground-cast cases.
--   * A GenSafe source consistency, a target consistency into a ground type,
--     and the two adjacent imprecision edges determine the missing ground
--     edge.
--   * This excludes the false arbitrary-inert formulation: a source ground
--     injection may change ℕ to ★ while the target stays at ℕ.
--   * Contains no cast classifier, result record, or residual-family API.

open import Types using (Ty; TyCtx; Ground; NonStar; ★)
import Imprecision as I
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (GenSafe)


MorePreciseGenSafeTargetGroundCastSquareᵀ : Set
MorePreciseGenSafeTargetGroundCastSquareᵀ = ∀ {Δ : TyCtx}
    {μ : I.ImpEnv Δ} {C A B G : Ty Δ}
    {νᴸ νᴿ : Env∼ Δ}
    {cᴸ : νᴸ ⊢ C ∼ A}
  → GenSafe cᴸ
  → Ground G
  → NonStar B
  → νᴿ ⊢ B ∼ G
  → μ I.⊢ C ⊑ B
  → μ I.⊢ A ⊑ ★
  → μ I.⊢ A ⊑ G
