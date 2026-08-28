{-# OPTIONS --safe #-}

module proof.DGG.notes.TargetOnlyNameRevealRebaseCounterexample where

-- File Charter:
--   * Gives a checked counterexample to transporting a pending target-only
--     instantiation name forward through a source reveal rebase.
--   * Uses the reachable Target Identity Reveal checkpoint where the open
--     beta rebase redirects the source pivot to the target-only beta pivot.
--   * Records why the instantiation worker needs a rebase-aware context or
--     zipper invariant before its target reveal-rebase branch can recurse.
--   * Changes no production relation or proof interface.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≢_)

open import proof.DGG.World
open import proof.DGG.SourceRebase using
  (SourceRebaseᶜ; source-rebase-now)
import proof.DGG.Examples.TargetIdentityReveal as TIR


-- Before the open beta rebase, target beta (X) has no aligned source
-- occupant.  Source alpha is aligned with the other target pivot (Y).
checkpoint₃-beta-target-only-before : ∀ Xᴸ
  → toRenameⁱ (ηᴸᶜ TIR.checkpoint₃-world) Xᴸ
    ≢ toRenameⁱ (ηᴿᶜ TIR.checkpoint₃-world) Fin.zero
checkpoint₃-beta-target-only-before Fin.zero ()


checkpoint₃-beta-rebase : SourceRebaseᶜ
    TIR.checkpoint₃-world TIR.checkpoint₃-beta-current
    Fin.zero Fin.zero
checkpoint₃-beta-rebase =
  source-rebase-now TIR.checkpoint₃-beta-ok
    TIR.checkpoint₃-beta-representation


-- After the rebase, the same target beta pivot (X) is aligned with source
-- alpha.  Thus target-only provenance is not preserved in this direction.
checkpoint₃-beta-target-only-after-impossible :
    (∀ Xᴸ
      → toRenameⁱ (ηᴸᶜ TIR.checkpoint₃-beta-current) Xᴸ
        ≢ toRenameⁱ (ηᴿᶜ TIR.checkpoint₃-beta-current) Fin.zero)
  → ⊥
checkpoint₃-beta-target-only-after-impossible target-only =
  target-only Fin.zero (pivot-alignedᵗ TIR.checkpoint₃-beta-ok)
