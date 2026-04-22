
{-

 The goal for this file is to prove the "fundamental" theorem of the logical relation
 in LogicalRelation.agda.

-}

module Parametricity where

-- File Charter:
--   * States the fundamental theorem of the logical relation for
--   * extrinsic-inst `PolyUpDown`.
--   * Keeps the main theorem postulated for now so downstream corollaries can
--   * be developed against the intended interface.
--   * Exports both the directional and two-direction formulations.

open import Types
open import Imprecision
open import Data.Product using (_,_)
open import TermPrecision
open import LogicalRelation

postulate
  fundamental :
    ∀ {E M M′ A B} {p : A ⊑ B} →
    (dir : Dir) →
    E ⊢ M ⊑ M′ ⦂ p →
    TPEnv.Γ E ∣ dir ⊨ M ⊑ M′ ⦂ p

fundamental-⊨ :
  ∀ {E M M′ A B} {p : A ⊑ B} →
  E ⊢ M ⊑ M′ ⦂ p →
  TPEnv.Γ E ⊨ M ⊑ M′ ⦂ p
fundamental-⊨ rel = (fundamental ≼ rel) , (fundamental ≽ rel)
