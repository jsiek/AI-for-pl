module proof.DGG.SourceStarProbe where

-- File Charter:
--   * Preserves the historical SourceStarCounterScratch snapshot as a
--     negative regression fixture under the inductive World design.
--   * The original snapshot aligned `X₀/Y₀` and `X₁/Y₁` in an identity
--     two-variable world, with both source entries equal to `★` and the
--     direct target entry for `Y₀` equal to `＇ Y₁`.
--   * Such a snapshot cannot form a live World: its first alignment
--     violates direct representation imprecision, and its second violates
--     dynamic-star source vacancy.  Both contradictions are exposed below.
--   * Its endpoint stores are each operationally possible, but compilation
--     and reduction from the empty world cannot produce this identity-aligned
--     relational snapshot.  It is adversarial interface evidence, not
--     reachability evidence.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using (TyStore; store-empty; store-bind)
open import Consistency using (_↪ᵗ_; empty; keep)
open import Imprecision using (ImpEnv; X⊑★)
import proof.DGG.CtxImp as CTX

private
  X₀ : TyVar 2
  X₀ = Fin.zero

  X₁ : TyVar 2
  X₁ = Fin.suc Fin.zero

  Y₀ : TyVar 2
  Y₀ = Fin.zero

  Y₁ : TyVar 2
  Y₁ = Fin.suc Fin.zero

------------------------------------------------------------------------
-- The original raw snapshot
------------------------------------------------------------------------

source-store : TyStore 2
source-store = store-bind (store-bind store-empty ★) ★

target-store : TyStore 2
target-store = store-bind (store-bind store-empty ★) (＇ Fin.zero)

probe-μ : ImpEnv 2
probe-μ Fin.zero = X⊑★
probe-μ (Fin.suc Fin.zero) = X⊑★

η-id : 2 ↪ᵗ 2
η-id = keep (keep empty)

-- Placement table:
--
--             X₀  X₁  Y₀  Y₁
--   original   0   1   0   1

OriginalWorldInvariants : Set
OriginalWorldInvariants =
  CTX.WorldInvariants η-id η-id probe-μ source-store target-store

------------------------------------------------------------------------
-- Independent invariant contradictions
------------------------------------------------------------------------

direct-representation-obstruction : OriginalWorldInvariants → ⊥
direct-representation-obstruction inv
    with CTX.representationsImprecise inv
      {Xᴸ = X₀} {Xᴿ = Y₀} refl
direct-representation-obstruction inv | ()

dynamic-star-vacancy-obstruction : OriginalWorldInvariants → ⊥
dynamic-star-vacancy-obstruction inv =
  CTX.dynamicStarSourcesUnoccupied inv X₁ refl refl Y₁ refl

no-original-world-invariants : ¬ OriginalWorldInvariants
no-original-world-invariants = direct-representation-obstruction

-- The original positive derivation package depended on precisely this raw
-- snapshot.  Keeping both contradictions checked prevents it from being
-- silently reinstated through a future compatibility constructor.
