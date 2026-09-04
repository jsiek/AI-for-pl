{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.SourceRebaseBackwardTypeTransportProbe where

-- File Charter:
--   * Tests backward type-imprecision transport across a direct source rebase.
--   * Uses the second reveal at checkpoint 1 of trusted Example 12.
--   * Shows that the current CTI lambda binder is related after the rebase,
--     although the same endpoint binder types are not related before it.
--   * Changes no live world, CTI, stack, or transport definition.

import Data.Fin as Fin
open import Relation.Nullary using (¬_)

open import Types using (＇_)
import Imprecision as I
import CastTerms as C
import TermCtx as TC
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.SourceRebase using
  (SourceRebaseᶜ; source-rebase-now)
open import proof.DGG.World using (_⊑ᵀ⟨_⟩_)
import proof.DGG.Examples.Example12 as Ex


-- In Example 12, the second reveal rebases source X from target X₁′ to Z′.
-- Thus X and Z′ are the same center variable only after this rebase.
checkpoint₁-beta-direct-rebase :
  SourceRebaseᶜ Ex.checkpoint₁-alpha-current
    Ex.checkpoint₁-beta-current Fin.zero Fin.zero
checkpoint₁-beta-direct-rebase =
  source-rebase-now Ex.checkpoint₁-beta-ok
    Ex.checkpoint₁-beta-representation


beta-binder-after :
  (＇ Fin.zero) ⊑ᵀ⟨ Ex.checkpoint₁-beta-current ⟩ (＇ Fin.zero)
beta-binder-after = I.X⊑X


beta-binder-before-impossible :
  ¬ ((＇ Fin.zero) ⊑ᵀ⟨ Ex.checkpoint₁-alpha-current ⟩
      (＇ Fin.zero))
beta-binder-before-impossible ()


-- This is the lambda at the bottom of the two reveal nodes in
-- Ex.checkpoint₁-imprecision.  Its binder premise is exactly the relation
-- above, so the obstructing geometry occurs in a typed current CTI lambda.
checkpoint₁-current-lambda :
  Ex.checkpoint₁-beta-current CTI.⊢²
    C.ƛ (C.` 0) ⊑ C.ƛ (C.` 0)
      ∶ I.⇒⊑⇒ beta-binder-after beta-binder-after
checkpoint₁-current-lambda =
  CTI.ƛ⊑ƛ²
    {A = ＇ Fin.zero} {A′ = ＇ Fin.zero}
    {B = ＇ Fin.zero} {B′ = ＇ Fin.zero}
    {pA = beta-binder-after} {pB = beta-binder-after}
    (CTI.x⊑x² {A = ＇ Fin.zero} {B = ＇ Fin.zero}
      {p = beta-binder-after} TC.Z TC.Z)


-- Pin the trusted enclosing derivation: it is the compiled checkpoint-1 pair
-- for Example 12 and contains checkpoint₁-current-lambda under the two direct
-- target reveal/rebase rules.
checkpoint₁-enclosing-derivation = Ex.checkpoint₁-imprecision
