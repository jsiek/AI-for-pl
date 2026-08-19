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
open import Data.Maybe using (just; nothing)
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)

open import Types using (TyCtx; Ty; TyVar; ★; ＇_; ⇑ᵗ)
open import TyStore using (lookupStore; lookupStore-∋)
open import Consistency using (id↪ᵗ; toRenameᵗ)
open import Conversion using (seal)
open import Imprecision using (ImpEnv; X⊑★)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.TargetExtend as TE
import proof.DGG.WorldInvariants as WI
open import proof.ImprecisionConsistency using (fin-suc-injective)

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

------------------------------------------------------------------------
-- Preservation deltas at target-only builders
------------------------------------------------------------------------

rightOnlyWorld-invariants : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} (B : Ty Δᴿ)
  → WI.WorldInvariants (CTI2.rightOnlyWorld W B)
  → WorldInvariants W
  → WorldInvariants (CTI2.rightOnlyWorld W B)
rightOnlyWorld-invariants {W = W} B stage1′ inv =
  world-invariants stage1′ preserve
  where
  preserve : ∀ Xᴸ
    → CTI2.impEnvʷ (CTI2.rightOnlyWorld W B)
        (toRenameᵗ (CTI2.ηᴸʷ (CTI2.rightOnlyWorld W B)) Xᴸ)
        ≡ X⊑★
    → lookupStore
        (CTI2.sourceStoreʷ (CTI2.rightOnlyWorld W B)) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ (CTI2.ηᴿʷ (CTI2.rightOnlyWorld W B)) Xᴿ
      ≢ toRenameᵗ (CTI2.ηᴸʷ (CTI2.rightOnlyWorld W B)) Xᴸ
  preserve Xᴸ mark entry Fin.zero ()
  preserve Xᴸ mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupied inv Xᴸ mark entry Xᴿ
      (fin-suc-injective aligned)

targetInsert-invariants : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ Consistency.↪ᵗ Δᴿ′} {π : Δ Consistency.↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
  → (ins : TE.TargetInsert ρ π W W′)
  → WI.WorldInvariants W′
  → WorldInvariants W
  → WorldInvariants W′
targetInsert-invariants {W = W} {W′ = W′} ins stage1′ inv =
  world-invariants stage1′ preserve
  where
  preserve : ∀ Xᴸ
    → CTI2.impEnvʷ W′ (toRenameᵗ (CTI2.ηᴸʷ W′) Xᴸ) ≡ X⊑★
    → lookupStore (CTI2.sourceStoreʷ W′) Xᴸ ≡ ★
    → ∀ Xᴿ′
    → toRenameᵗ (CTI2.ηᴿʷ W′) Xᴿ′
      ≢ toRenameᵗ (CTI2.ηᴸʷ W′) Xᴸ
  preserve Xᴸ mark entry Xᴿ′ aligned
      with TE.target-source-reflect ins (sym aligned)
  preserve Xᴸ mark entry Xᴿ′ aligned
      | Xᴿ , Xᴿ′-eq , old-aligned =
    dynamicStarSourcesUnoccupied inv Xᴸ old-mark old-entry Xᴿ
      (sym old-aligned)
    where
    old-mark :
      CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ) ≡ X⊑★
    old-mark = trans
      (sym (TE.impEnv-insert ins (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)))
      (trans
        (cong (CTI2.impEnvʷ W′) (sym (TE.source-insert ins Xᴸ))) mark)

    old-entry : lookupStore (CTI2.sourceStoreʷ W) Xᴸ ≡ ★
    old-entry = trans
      (sym (cong (λ Σ → lookupStore Σ Xᴸ) (TE.sourceStore-kept ins)))
      entry

smartAlias-fresh-source-not-star : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → CTI2.SmartAliasMergeGuard W Wᵐ β α
  → lookupStore (CTI2.sourceStoreʷ Wᵐ) Fin.zero ≢ ★
smartAlias-fresh-source-not-star guard entry =
  variable≢star
    (trans
      (sym (cong (λ Σ → lookupStore Σ Fin.zero)
        (CTI2.SmartAliasMergeGuard.sourceStore-lifted guard)))
      entry)

------------------------------------------------------------------------
-- Rule-premise payoff
------------------------------------------------------------------------

world-invariants-no-target-at-dynamic-star : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
  → WorldInvariants W
  → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) X) ≡ X⊑★
  → lookupStore (CTI2.sourceStoreʷ W) X ≡ ★
  → CTI2.NoTargetOccupantAtSource W X
world-invariants-no-target-at-dynamic-star {X = X} inv mark entry
    (Xᴿ , aligned) =
  dynamicStarSourcesUnoccupied inv X mark entry Xᴿ aligned

world-invariants-see-through-premise : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTI2.World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
  → WorldInvariants W′
  → CTI2.TagRebaseAtᴸ W′ W (just X) nothing
  → CTI2.sourceStoreʷ W CTI2.⊢↓[ just X ] seal X ★
  → CTI2.NoTargetOccupantAtSource W′ X
world-invariants-see-through-premise inv
    (CTI2.tag-rebase-onlyᴸ mark disaligned represented)
    (CTI2.⊢↓-sealˣ source∋) =
  world-invariants-no-target-at-dynamic-star inv mark
    (lookupStore-∋ source∋)

world-invariants-d17c-occupancy : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
  → WorldInvariants W
  → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) X) ≡ X⊑★
  → lookupStore (CTI2.sourceStoreʷ W) X ≡ ★
  → CTI2.Occupied W (toRenameᵗ (CTI2.ηᴸʷ W) X) → ⊥
world-invariants-d17c-occupancy inv mark entry =
  world-invariants-no-target-at-dynamic-star inv mark entry
