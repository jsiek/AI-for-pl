module T15Invariant5ReconProbe where

-- File Charter:
--   * Drafts D16 invariant (5) as an extension of the live Stage 1
--     WorldInvariants companion, without changing the live relation.
--   * Uses total direct store lookup, matching the three landed fields.
--   * Checks preservation pressure points, payoff lemmas, and kill checks
--     added by the T15 recon addendum.
--   * Contains no implementation of the eventual World migration.

open import Data.Empty using (⊥)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)

open import Types using (TyCtx; Ty; TyVar; ★; ＇_; ⇑ᵗ)
open import TyStore using (lookupStore)
open import Consistency using (id↪ᵗ; toRenameᵗ)
open import Imprecision using (ImpEnv; X⊑★)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.WorldInvariants as WI

------------------------------------------------------------------------
-- Proposed Stage 1 companion
------------------------------------------------------------------------

record WorldInvariants {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) : Set where
  constructor world-invariants
  field
    stage1 : WI.WorldInvariants W

    dynamicStarSourcesUnoccupied :
      ∀ (Xᴸ : TyVar Δᴸ)
      → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ) ≡ X⊑★
      → lookupStore (CTI2.sourceStoreʷ W) Xᴸ ≡ ★
      → ∀ (Xᴿ : TyVar Δᴿ)
      → toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
        ≢ toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ

open WorldInvariants public

------------------------------------------------------------------------
-- Empty initial world
------------------------------------------------------------------------

emptyStore-lookup-variable : ∀ {Δ} (X : TyVar Δ)
  → lookupStore (WI.emptyStore Δ) X ≡ ＇ X
emptyStore-lookup-variable {Nat.suc Δ} Fin.zero = refl
emptyStore-lookup-variable {Nat.suc Δ} (Fin.suc X) =
  cong ⇑ᵗ (emptyStore-lookup-variable X)

variable≢star : ∀ {Δ} {X : TyVar Δ}
  → _≡_ {A = Ty Δ} (＇ X) ★ → ⊥
variable≢star ()

initialWorld-invariants : ∀ {Δ} (mu : ImpEnv Δ)
  → WorldInvariants (WI.initialWorld mu)
initialWorld-invariants {Δ = Δ} mu = world-invariants
  (WI.initialWorld-invariants mu) no-dynamic-star-source
  where
  no-dynamic-star-source : ∀ (Xᴸ : TyVar Δ)
    → mu (toRenameᵗ id↪ᵗ Xᴸ) ≡ X⊑★
    → lookupStore (WI.emptyStore Δ) Xᴸ ≡ ★
    → ∀ (Xᴿ : TyVar Δ)
    → toRenameᵗ id↪ᵗ Xᴿ ≢ toRenameᵗ id↪ᵗ Xᴸ
  no-dynamic-star-source Xᴸ mark entry Xᴿ aligned =
    variable≢star (trans (sym (emptyStore-lookup-variable Xᴸ)) entry)
