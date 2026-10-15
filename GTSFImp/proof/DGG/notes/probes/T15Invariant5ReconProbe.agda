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
open import TyStore using
  (TyStore; store-empty; store-bind; lookupStore; lookupStore-∋)
open import Consistency using
  (_↪ᵗ_; empty; keep; id↪ᵗ; toRenameᵗ)
open import Conversion using (seal)
import Conversion as Conv
open import Imprecision using (ImpEnv; X⊑★)
import proof.DGG.CtxImp as CTX
import proof.DGG.TargetExtend as TE
import proof.DGG.WorldInvariants as WI
open import proof.ImprecisionConsistency using (fin-suc-injective)

------------------------------------------------------------------------
-- Proposed Stage 1 companion
------------------------------------------------------------------------

record WorldInvariants {Δᴸ Δᴿ Δ}
    (W : CTX.World Δᴸ Δᴿ Δ) : Set where
  constructor world-invariants
  field
    stage1 : WI.WorldInvariants W

    dynamicStarSourcesUnoccupied :
      ∀ (Xᴸ : TyVar Δᴸ)
      → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
      → lookupStore (CTX.sourceStoreʷ W) Xᴸ ≡ ★
      → ∀ (Xᴿ : TyVar Δᴿ)
      → toRenameᵗ (CTX.ηᴿʷ W) Xᴿ
        ≢ toRenameᵗ (CTX.ηᴸʷ W) Xᴸ

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
    {W : CTX.World Δᴸ Δᴿ Δ} (B : Ty Δᴿ)
  → WI.WorldInvariants (CTX.rightOnlyWorld W B)
  → WorldInvariants W
  → WorldInvariants (CTX.rightOnlyWorld W B)
rightOnlyWorld-invariants {W = W} B stage1′ inv =
  world-invariants stage1′ preserve
  where
  preserve : ∀ Xᴸ
    → CTX.impEnvʷ (CTX.rightOnlyWorld W B)
        (toRenameᵗ (CTX.ηᴸʷ (CTX.rightOnlyWorld W B)) Xᴸ)
        ≡ X⊑★
    → lookupStore
        (CTX.sourceStoreʷ (CTX.rightOnlyWorld W B)) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ (CTX.ηᴿʷ (CTX.rightOnlyWorld W B)) Xᴿ
      ≢ toRenameᵗ (CTX.ηᴸʷ (CTX.rightOnlyWorld W B)) Xᴸ
  preserve Xᴸ mark entry Fin.zero ()
  preserve Xᴸ mark entry (Fin.suc Xᴿ) aligned =
    dynamicStarSourcesUnoccupied inv Xᴸ mark entry Xᴿ
      (fin-suc-injective aligned)

targetInsert-invariants : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {ρ : Δᴿ Consistency.↪ᵗ Δᴿ′} {π : Δ Consistency.↪ᵗ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
  → (ins : TE.TargetInsert ρ π W W′)
  → WI.WorldInvariants W′
  → WorldInvariants W
  → WorldInvariants W′
targetInsert-invariants {W = W} {W′ = W′} ins stage1′ inv =
  world-invariants stage1′ preserve
  where
  preserve : ∀ Xᴸ
    → CTX.impEnvʷ W′ (toRenameᵗ (CTX.ηᴸʷ W′) Xᴸ) ≡ X⊑★
    → lookupStore (CTX.sourceStoreʷ W′) Xᴸ ≡ ★
    → ∀ Xᴿ′
    → toRenameᵗ (CTX.ηᴿʷ W′) Xᴿ′
      ≢ toRenameᵗ (CTX.ηᴸʷ W′) Xᴸ
  preserve Xᴸ mark entry Xᴿ′ aligned
      with TE.target-source-reflect ins (sym aligned)
  preserve Xᴸ mark entry Xᴿ′ aligned
      | Xᴿ , Xᴿ′-eq , old-aligned =
    dynamicStarSourcesUnoccupied inv Xᴸ old-mark old-entry Xᴿ
      (sym old-aligned)
    where
    old-mark :
      CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
    old-mark = trans
      (sym (TE.impEnv-insert ins (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ)))
      (trans
        (cong (CTX.impEnvʷ W′) (sym (TE.source-insert ins Xᴸ))) mark)

    old-entry : lookupStore (CTX.sourceStoreʷ W) Xᴸ ≡ ★
    old-entry = trans
      (sym (cong (λ Σ → lookupStore Σ Xᴸ) (TE.sourceStore-kept ins)))
      entry

smartAlias-fresh-source-not-star : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTX.World (Nat.suc Δᴸ) Δᴿ Δ} {β α}
  → CTX.SmartAliasMergeGuard W Wᵐ β α
  → lookupStore (CTX.sourceStoreʷ Wᵐ) Fin.zero ≢ ★
smartAlias-fresh-source-not-star guard entry =
  variable≢star
    (trans
      (sym (cong (λ Σ → lookupStore Σ Fin.zero)
        (CTX.SmartAliasMergeGuard.sourceStore-lifted guard)))
      entry)

------------------------------------------------------------------------
-- Rule-premise payoff
------------------------------------------------------------------------

world-invariants-no-target-at-dynamic-star : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
  → WorldInvariants W
  → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) X) ≡ X⊑★
  → lookupStore (CTX.sourceStoreʷ W) X ≡ ★
  → CTX.NoTargetOccupantAtSource W X
world-invariants-no-target-at-dynamic-star {X = X} inv mark entry
    (Xᴿ , aligned) =
  dynamicStarSourcesUnoccupied inv X mark entry Xᴿ aligned

world-invariants-see-through-premise : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : CTX.World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
  → WorldInvariants W′
  → CTX.TagRebaseAtᴸ W′ W (just X) nothing
  → CTX.sourceStoreʷ W Conv.⊢↓[ just X ] seal X ★
  → CTX.NoTargetOccupantAtSource W′ X
world-invariants-see-through-premise inv
    (CTX.tag-rebase-onlyᴸ mark disaligned represented)
    (Conv.⊢↓-sealˣ source∋) =
  world-invariants-no-target-at-dynamic-star inv mark
    (lookupStore-∋ source∋)

world-invariants-d17c-occupancy : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
  → WorldInvariants W
  → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) X) ≡ X⊑★
  → lookupStore (CTX.sourceStoreʷ W) X ≡ ★
  → CTX.Occupied W (toRenameᵗ (CTX.ηᴸʷ W) X) → ⊥
world-invariants-d17c-occupancy inv mark entry =
  world-invariants-no-target-at-dynamic-star inv mark entry

------------------------------------------------------------------------
-- Kill checks
------------------------------------------------------------------------

projection-mismatch-store : TyStore 1
projection-mismatch-store = store-bind store-empty ★

projection-mismatch-env : ImpEnv 1
projection-mismatch-env Fin.zero = X⊑★

projection-mismatch-world : CTX.World 1 1 1
projection-mismatch-world =
  CTX.world (keep empty) (keep empty) projection-mismatch-env
    projection-mismatch-store projection-mismatch-store

projection-mismatch-stage1 : WI.WorldInvariants projection-mismatch-world
projection-mismatch-stage1 =
  WI.identityWorld-invariants projection-mismatch-env
    projection-mismatch-store

projection-mismatch-rejects-invariant5 :
  WorldInvariants projection-mismatch-world → ⊥
projection-mismatch-rejects-invariant5 inv =
  dynamicStarSourcesUnoccupied inv Fin.zero refl refl Fin.zero refl

s-occ-aligned-stage1 : WI.WorldInvariants projection-mismatch-world
s-occ-aligned-stage1 = projection-mismatch-stage1

s-occ-aligned-rejects-invariant5 :
  WorldInvariants projection-mismatch-world → ⊥
s-occ-aligned-rejects-invariant5 inv =
  dynamicStarSourcesUnoccupied inv Fin.zero refl refl Fin.zero refl

s-occ-prealignment-world : CTX.World 1 0 1
s-occ-prealignment-world =
  CTX.world (keep empty) empty (λ { Fin.zero → X⊑★ })
    (store-bind store-empty ★) store-empty

s-occ-prealignment-stage1 : WI.WorldInvariants s-occ-prealignment-world
s-occ-prealignment-stage1 =
  WI.world-invariants
    (λ { Fin.zero () })
    (λ { {Xᴿ = ()} })
    (λ ())

s-occ-prealignment-invariants : WorldInvariants s-occ-prealignment-world
s-occ-prealignment-invariants =
  world-invariants s-occ-prealignment-stage1 no-target
  where
  no-target : ∀ Xᴸ
    → CTX.impEnvʷ s-occ-prealignment-world
        (toRenameᵗ (CTX.ηᴸʷ s-occ-prealignment-world) Xᴸ) ≡ X⊑★
    → lookupStore (CTX.sourceStoreʷ s-occ-prealignment-world) Xᴸ ≡ ★
    → ∀ Xᴿ
    → toRenameᵗ (CTX.ηᴿʷ s-occ-prealignment-world) Xᴿ
      ≢ toRenameᵗ (CTX.ηᴸʷ s-occ-prealignment-world) Xᴸ
  no-target Fin.zero mark entry ()
