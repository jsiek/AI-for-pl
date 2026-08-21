module proof.DGG.CenterCrossingProbe where

-- File Charter:
--   * Preserves the historical target-seal center-crossing snapshots as
--     negative regressions for the live World invariants.
--   * The source endpoint store (`bind ★; bind ★`) and target endpoint store
--     (`bind ★; bind ＇0`) are each operationally possible, but compilation
--     and reduction from the empty world cannot produce the raw relational
--     alignments below.
--   * `W` and `W′` fail direct representation imprecision; `Wᵖ` also puts a
--     dynamic-star source at an occupied center.  Thus the old positive
--     target-seal premise was adversarial interface evidence, not a reachable
--     DGG checkpoint.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using (TyStore; store-empty; store-bind)
open import Consistency using (_↪ᵗ_; empty; keep; skip)
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
-- The original raw snapshots
------------------------------------------------------------------------

source-store : TyStore 2
source-store = store-bind (store-bind store-empty ★) ★

target-store : TyStore 2
target-store = store-bind (store-bind store-empty ★) (＇ Fin.zero)

probe-μ : ImpEnv 3
probe-μ Fin.zero = X⊑★
probe-μ (Fin.suc Fin.zero) = X⊑★
probe-μ (Fin.suc (Fin.suc Fin.zero)) = X⊑★

ηᴸ-ab : 2 ↪ᵗ 3
ηᴸ-ab = keep (keep (skip empty))

ηᴸ-ac : 2 ↪ᵗ 3
ηᴸ-ac = keep (skip (keep empty))

ηᴿ-ac : 2 ↪ᵗ 3
ηᴿ-ac = keep (skip (keep empty))

ηᴿ-bc : 2 ↪ᵗ 3
ηᴿ-bc = skip (keep (keep empty))

-- Placement table:
--
--             X₀  X₁  Y₀  Y₁
--   W          a   b   a   c
--   W′         a   b   b   c
--   Wᵖ         a   c   b   c

OriginalWInvariants : Set
OriginalWInvariants =
  CTX.WorldInvariants ηᴸ-ab ηᴿ-ac probe-μ source-store target-store

OriginalW′Invariants : Set
OriginalW′Invariants =
  CTX.WorldInvariants ηᴸ-ab ηᴿ-bc probe-μ source-store target-store

OriginalWᵖInvariants : Set
OriginalWᵖInvariants =
  CTX.WorldInvariants ηᴸ-ac ηᴿ-bc probe-μ source-store target-store

------------------------------------------------------------------------
-- Checked invariant contradictions
------------------------------------------------------------------------

W-direct-representation-obstruction : OriginalWInvariants → ⊥
W-direct-representation-obstruction inv
    with CTX.representationsImprecise inv
      {Xᴸ = X₀} {Xᴿ = Y₀} refl
W-direct-representation-obstruction inv | ()

W′-direct-representation-obstruction : OriginalW′Invariants → ⊥
W′-direct-representation-obstruction inv
    with CTX.representationsImprecise inv
      {Xᴸ = X₁} {Xᴿ = Y₀} refl
W′-direct-representation-obstruction inv | ()

Wᵖ-dynamic-star-vacancy-obstruction : OriginalWᵖInvariants → ⊥
Wᵖ-dynamic-star-vacancy-obstruction inv =
  CTX.dynamicStarSourcesUnoccupied inv X₁ refl refl Y₁ refl

no-original-W-invariants : ¬ OriginalWInvariants
no-original-W-invariants = W-direct-representation-obstruction

no-original-W′-invariants : ¬ OriginalW′Invariants
no-original-W′-invariants = W′-direct-representation-obstruction

no-original-Wᵖ-invariants : ¬ OriginalWᵖInvariants
no-original-Wᵖ-invariants = Wᵖ-dynamic-star-vacancy-obstruction
