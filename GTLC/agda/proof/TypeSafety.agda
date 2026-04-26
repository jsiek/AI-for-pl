module proof.TypeSafety where

-- File Charter:
--   * Private GTLC type-safety theorem via compilation to cast calculus.
--   * Delegates runtime safety to `proof.CastSafety`.

open import Agda.Builtin.List using ([])
open import Data.Product using (∃; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Types
open import GTLC
open import CastCalculus
open import Compile
open import proof.CompileMeta using (compile-preserves)

import proof.CastSafety as CastSafetyProof

type-safety
  : {M : Term} {A : Ty} {N : Termᶜ}
  → (M⦂A : [] ⊢ M ⦂ A)
  → compile M⦂A —↠ᶜ N
  → (∃[ N′ ] (N —→ᶜ N′)) ⊎ Result N
type-safety M⦂A M—↠N = CastSafetyProof.type-safetyᶜ (compile-preserves M⦂A) M—↠N
