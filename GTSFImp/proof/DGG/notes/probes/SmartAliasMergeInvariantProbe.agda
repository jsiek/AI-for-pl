module proof.DGG.notes.probes.SmartAliasMergeInvariantProbe where

-- File Charter:
--   * Records the direct-representation obstruction in the old D1
--     smart-alias-merge fixture.
--   * Shows that aligning a structurally lifted source head with β is
--     incompatible with the target binding β := α under WorldInvariants.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (refl)

open import Types using (★; ＇_)
open import TyStore using (store-empty; store-lift; store-bind)
open import Consistency using (empty; keep; skip)
import Imprecision as I
import proof.DGG.CtxImp as CTX


all-dynamic : I.ImpEnv 3
all-dynamic _ = I.X⊑★


smart-alias-invariants-impossible :
  CTX.WorldInvariants
    (keep (skip (keep empty)))
    (keep (keep (skip empty)))
    all-dynamic
    (store-lift (store-lift store-empty))
    (store-bind (store-bind store-empty ★) (＇ Fin.zero))
  → ⊥
smart-alias-invariants-impossible inv
    with CTX.representationsImprecise inv
      {Xᴸ = Fin.zero} {Xᴿ = Fin.zero} refl
smart-alias-invariants-impossible inv | ()
