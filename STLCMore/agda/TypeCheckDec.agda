module TypeCheckDec where

-- File Charter:
--   * Public statement of decidable type checking for STLCMore.
--   * Proof/algorithm details live in `proof/TypeCheckDec.agda`.

open import Data.Product using (∃; ∃-syntax)
open import Relation.Nullary using (Dec)
open import STLCMore

import proof.TypeCheckDec as Proof

type-check : (Γ : Ctx) (M : Term) → Dec (∃[ A ] Γ ⊢ M ⦂ A)
type-check = Proof.type-check

type-check-expect : (Γ : Ctx) (M : Term) (A : Ty) → Dec (Γ ⊢ M ⦂ A)
type-check-expect = Proof.type-check-expect
