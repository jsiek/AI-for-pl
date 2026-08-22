module proof.DGG.notes.probes.T11TargetInsertPositionProbe where

-- File Charter:
--   * Records the target-center position of the fresh target variable for
--     direct right binds and for right binds lifted under a source-only binder.
--   * The checked equalities support the T11 meet-point feasibility note.

import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty)
open import Consistency using (toRenameᵗ)
open import Imprecision using (X⊑★)
import proof.DGG.CtxImp as CTI2


direct-right-bind-fresh-target-center : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → toRenameᵗ (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W B)) Fin.zero
      ≡ Fin.zero
direct-right-bind-fresh-target-center = refl


lift-left-around-right-bind-fresh-target-center : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → toRenameᵗ
      (CTI2.ηᴿʷ
        (CTI2.liftWorldLeft X⊑★ (CTI2.rightOnlyWorld W B)))
      Fin.zero
      ≡ Fin.suc Fin.zero
lift-left-around-right-bind-fresh-target-center = refl


parked-right-bind-after-lift-left-fresh-target-center : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → toRenameᵗ
      (CTI2.ηᴿʷ
        (CTI2.rightOnlyWorld (CTI2.liftWorldLeft X⊑★ W) B))
      Fin.zero
      ≡ Fin.zero
parked-right-bind-after-lift-left-fresh-target-center = refl
