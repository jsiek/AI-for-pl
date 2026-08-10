module SrcConsistBlocked where

-- Scratch witness for the source-consistency gate that blocks
-- (ΛX. λx:X. (λy:★. y) · x).
--
-- This file is expected not to type-check under the current GTSFImp
-- consistency relation: source consistency uses idᶜ, so the bound type
-- variable has mode X∼X, while the needed argument consistency is ★ ∼ ＇0.

import Data.Fin as Fin
open import Data.List using ([]; _∷_)

open import Types
open import TermCtx using (Z)
open import GradualTerms
open import Consistency

blocked-gate : _∼_ {Δ = 1} ★ (＇ Fin.zero)
blocked-gate = ？ (id (＇ Fin.zero))

blocked-term : GTerm 0
blocked-term =
  Λ (ƛ ＇ Fin.zero ⇒ ((ƛ ★ ⇒ ` 0) ·[ 0 ] ` 0))

blocked-typing :
  0 ∣ [] ⊢ blocked-term ⦂ `∀ (＇ Fin.zero ⇒ ★)
blocked-typing =
  ⊢Λ
    (ƛ ＇ Fin.zero ⇒ ((ƛ ★ ⇒ ` 0) ·[ 0 ] ` 0))
    (⊢ƛ (⊢· (⊢ƛ (⊢` Z)) (⊢` Z) blocked-gate))
