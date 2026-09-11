module T15WorldInvariantsDesignProbe where

-- File Charter:
--   * Type-checks the D16 eight-field World record and empty-store
--     initialWorld draft without changing the live relation.
--   * States the strict and chain-permissive direct-entry alternatives for
--     unmatched target pivots and checks the recommended permissive form.
--   * Reconstructs the D8a and T10 Probe 1 rebase worlds and checks whether
--     their representation pairs satisfy all three drafted additions.
--   * Contains no implementation of the World migration.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong)

open import Types using
  (TyCtx; Ty; TyVar; ★; ＇_; ‵_; `ℕ; renameᵗ; ⇑ᵗ)
open import TyStore using (TyStore; store-empty; store-lift; store-bind)
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; id↪ᵗ; toRenameᵗ)
open import Imprecision using
  (ImpEnv; X⊑X; X⊑★; extendᵐ; instᵐ; _⊢_⊑_; ★⊑★; ι⊑ι)
open import proof.ImprecisionConsistency using
  (refl⊑; toRenameᵗ-injective)

------------------------------------------------------------------------
-- Total, one-step store lookup
------------------------------------------------------------------------

-- TyStore's relational lookup has no entry for a structurally lifted zero.
-- This total view treats that zero as its own one-step representation and
-- otherwise returns exactly the direct entry, lifted into the current scope.

lookupStore : ∀ {Δ} → TyStore Δ → TyVar Δ → Ty Δ
lookupStore (store-lift Σ) Fin.zero = ＇ Fin.zero
lookupStore (store-lift Σ) (Fin.suc X) = ⇑ᵗ (lookupStore Σ X)
lookupStore (store-bind Σ A) Fin.zero = ⇑ᵗ A
lookupStore (store-bind Σ A) (Fin.suc X) = ⇑ᵗ (lookupStore Σ X)

------------------------------------------------------------------------
-- Draft record
------------------------------------------------------------------------

record World (Δᴸ Δᴿ Δ : TyCtx) : Set where
  constructor world
  field
    ηᴸʷ : Δᴸ ↪ᵗ Δ
    ηᴿʷ : Δᴿ ↪ᵗ Δ
    impEnvʷ : ImpEnv Δ
    sourceStoreʷ : TyStore Δᴸ
    targetStoreʷ : TyStore Δᴿ

    preciseMarksAlignedʷ :
      ∀ (Xᴸ : TyVar Δᴸ)
      → impEnvʷ (toRenameᵗ ηᴸʷ Xᴸ) ≡ X⊑X
      → Σ[ Xᴿ ∈ TyVar Δᴿ ]
          toRenameᵗ ηᴿʷ Xᴿ ≡ toRenameᵗ ηᴸʷ Xᴸ

    representationsImpreciseʷ :
      ∀ {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → toRenameᵗ ηᴸʷ Xᴸ ≡ toRenameᵗ ηᴿʷ Xᴿ
      → impEnvʷ ⊢
          renameᵗ (toRenameᵗ ηᴸʷ)
            (lookupStore sourceStoreʷ Xᴸ)
          ⊑ renameᵗ (toRenameᵗ ηᴿʷ)
            (lookupStore targetStoreʷ Xᴿ)

    unmatchedTargetsDynamicʷ :
      ∀ (Xᴿ : TyVar Δᴿ)
      → (∀ (Xᴸ : TyVar Δᴸ)
          → toRenameᵗ ηᴸʷ Xᴸ ≢ toRenameᵗ ηᴿʷ Xᴿ)
      → lookupStore targetStoreʷ Xᴿ ≡ ★
        ⊎ Σ[ Yᴿ ∈ TyVar Δᴿ ]
            (lookupStore targetStoreʷ Xᴿ ≡ ＇ Yᴿ)
          × (∀ (Xᴸ : TyVar Δᴸ)
              → toRenameᵗ ηᴸʷ Xᴸ ≢ toRenameᵗ ηᴿʷ Yᴿ)

open World public

CenterAligned : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δᴸ
  → TyVar Δᴿ
  → Set
CenterAligned W Xᴸ Xᴿ =
  toRenameᵗ (ηᴸʷ W) Xᴸ ≡ toRenameᵗ (ηᴿʷ W) Xᴿ

RepresentationInvariant : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → Set
RepresentationInvariant W =
  ∀ {Xᴸ Xᴿ} → CenterAligned W Xᴸ Xᴿ
  → impEnvʷ W ⊢
      renameᵗ (toRenameᵗ (ηᴸʷ W))
        (lookupStore (sourceStoreʷ W) Xᴸ)
      ⊑ renameᵗ (toRenameᵗ (ηᴿʷ W))
        (lookupStore (targetStoreʷ W) Xᴿ)

representationInvariant : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
  → RepresentationInvariant W
representationInvariant W = representationsImpreciseʷ W

-- When related direct entries are both variables, type-imprecision forces
-- their heads to share a center.  Applying the field again supplies the next
-- direct-entry relation; finite store age then supports induction down a
-- complete representation chain.

imprecision-cong : ∀ {Δ} {μ : ImpEnv Δ} {A A′ B B′ : Ty Δ}
  → A ≡ A′
  → B ≡ B′
  → μ ⊢ A ⊑ B
  → μ ⊢ A′ ⊑ B′
imprecision-cong refl refl A⊑B = A⊑B

variableHeadsAlign : ∀ {Δ} {μ : ImpEnv Δ} {X Y : TyVar Δ}
  → μ ⊢ ＇ X ⊑ ＇ Y
  → X ≡ Y
variableHeadsAlign X⊑X = refl

variableEntryChainCoherence : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
    {Xᴸ Yᴸ : TyVar Δᴸ} {Xᴿ Yᴿ : TyVar Δᴿ}
  → CenterAligned W Xᴸ Xᴿ
  → lookupStore (sourceStoreʷ W) Xᴸ ≡ ＇ Yᴸ
  → lookupStore (targetStoreʷ W) Xᴿ ≡ ＇ Yᴿ
  → CenterAligned W Yᴸ Yᴿ
    × (impEnvʷ W ⊢
        renameᵗ (toRenameᵗ (ηᴸʷ W))
          (lookupStore (sourceStoreʷ W) Yᴸ)
        ⊑ renameᵗ (toRenameᵗ (ηᴿʷ W))
          (lookupStore (targetStoreʷ W) Yᴿ))
variableEntryChainCoherence W {Yᴸ = Yᴸ} {Yᴿ = Yᴿ}
    aligned source-entry target-entry =
  heads-aligned , representationsImpreciseʷ W heads-aligned
  where
  heads-aligned : CenterAligned W Yᴸ Yᴿ
  heads-aligned = variableHeadsAlign
    (imprecision-cong
      (cong (renameᵗ (toRenameᵗ (ηᴸʷ W))) source-entry)
      (cong (renameᵗ (toRenameᵗ (ηᴿʷ W))) target-entry)
      (representationsImpreciseʷ W aligned))

-- The strict candidate is stronger than the record's recommended
-- chain-permissive field.

strictImpliesChainPermissive : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
  → (∀ (Xᴿ : TyVar Δᴿ)
      → (∀ (Xᴸ : TyVar Δᴸ)
          → toRenameᵗ (ηᴸʷ W) Xᴸ
            ≢ toRenameᵗ (ηᴿʷ W) Xᴿ)
      → lookupStore (targetStoreʷ W) Xᴿ ≡ ★)
  → ∀ (Xᴿ : TyVar Δᴿ)
  → (∀ (Xᴸ : TyVar Δᴸ)
      → toRenameᵗ (ηᴸʷ W) Xᴸ
        ≢ toRenameᵗ (ηᴿʷ W) Xᴿ)
  → lookupStore (targetStoreʷ W) Xᴿ ≡ ★
    ⊎ Σ[ Yᴿ ∈ TyVar Δᴿ ]
        (lookupStore (targetStoreʷ W) Xᴿ ≡ ＇ Yᴿ)
      × (∀ (Xᴸ : TyVar Δᴸ)
          → toRenameᵗ (ηᴸʷ W) Xᴸ
            ≢ toRenameᵗ (ηᴿʷ W) Yᴿ)
strictImpliesChainPermissive strict Xᴿ unmatched =
  inj₁ (strict Xᴿ unmatched)

------------------------------------------------------------------------
-- Empty compilation stores and the amended initial world
------------------------------------------------------------------------

emptyStore : (Δ : TyCtx) → TyStore Δ
emptyStore Nat.zero = store-empty
emptyStore (Nat.suc Δ) = store-lift (emptyStore Δ)

initialRepresentations : ∀ {Δ} {μ : ImpEnv Δ} {Xᴸ Xᴿ : TyVar Δ}
  → toRenameᵗ id↪ᵗ Xᴸ ≡ toRenameᵗ id↪ᵗ Xᴿ
  → μ ⊢
      renameᵗ (toRenameᵗ id↪ᵗ)
        (lookupStore (emptyStore Δ) Xᴸ)
      ⊑ renameᵗ (toRenameᵗ id↪ᵗ)
        (lookupStore (emptyStore Δ) Xᴿ)
initialRepresentations {Xᴸ = Xᴸ} aligned
    with toRenameᵗ-injective id↪ᵗ aligned
initialRepresentations {Xᴸ = Xᴸ} aligned | refl = refl⊑ _

initialUnmatchedTargets : ∀ {Δ} (Xᴿ : TyVar Δ)
  → (∀ (Xᴸ : TyVar Δ)
      → toRenameᵗ id↪ᵗ Xᴸ ≢ toRenameᵗ id↪ᵗ Xᴿ)
  → lookupStore (emptyStore Δ) Xᴿ ≡ ★
    ⊎ Σ[ Yᴿ ∈ TyVar Δ ]
        (lookupStore (emptyStore Δ) Xᴿ ≡ ＇ Yᴿ)
      × (∀ (Xᴸ : TyVar Δ)
          → toRenameᵗ id↪ᵗ Xᴸ ≢ toRenameᵗ id↪ᵗ Yᴿ)
initialUnmatchedTargets Xᴿ unmatched =
  ⊥-elim (unmatched Xᴿ refl)

initialWorld : ∀ {Δ} → ImpEnv Δ → World Δ Δ Δ
initialWorld {Δ} μ =
  world id↪ᵗ id↪ᵗ μ (emptyStore Δ) (emptyStore Δ)
    (λ Xᴸ precise → Xᴸ , refl)
    initialRepresentations initialUnmatchedTargets

initialWorld-source-empty : ∀ {Δ} (μ : ImpEnv Δ)
  → sourceStoreʷ (initialWorld μ) ≡ emptyStore Δ
initialWorld-source-empty μ = refl

initialWorld-target-empty : ∀ {Δ} (μ : ImpEnv Δ)
  → targetStoreʷ (initialWorld μ) ≡ emptyStore Δ
initialWorld-target-empty μ = refl

emptyStore-under-binder : ∀ {Δ}
  → emptyStore (Nat.suc Δ) ≡ store-lift (emptyStore Δ)
emptyStore-under-binder = refl

------------------------------------------------------------------------
-- D8a reconstruction: both rebase endpoints violate invariant (4)
------------------------------------------------------------------------

empty-μ : ImpEnv 0
empty-μ ()

μ₂ : ImpEnv 2
μ₂ = instᵐ (extendᵐ X⊑X empty-μ)

source-η-old : 1 ↪ᵗ 2
source-η-old = skip (keep empty)

source-η-fresh : 1 ↪ᵗ 2
source-η-fresh = keep empty

target-η-id : 2 ↪ᵗ 2
target-η-id = keep (keep empty)

source-η-empty : 0 ↪ᵗ 2
source-η-empty = skip (skip empty)

ℕ₀ : Ty 0
ℕ₀ = ‵ `ℕ

ℕ₁ : Ty 1
ℕ₁ = ‵ `ℕ

d8a-source-store : TyStore 1
d8a-source-store = store-bind store-empty ℕ₀

d8a-target-store : TyStore 2
d8a-target-store = store-bind (store-bind store-empty ℕ₀) ℕ₁

d8a-fresh-direct-entry :
  lookupStore d8a-target-store Fin.zero ≡ ‵ `ℕ
d8a-fresh-direct-entry = refl

d8a-old-direct-entry :
  lookupStore d8a-target-store (Fin.suc Fin.zero) ≡ ‵ `ℕ
d8a-old-direct-entry = refl

------------------------------------------------------------------------
-- The live ★-then-variable route needs chain-permissive unmatched targets
------------------------------------------------------------------------

alias-chain-target-store : TyStore 2
alias-chain-target-store =
  store-bind (store-bind store-empty ★) (＇ Fin.zero)

alias-chain-precise :
  ∀ (Xᴸ : TyVar 0)
  → μ₂ (toRenameᵗ source-η-empty Xᴸ) ≡ X⊑X
  → Σ[ Xᴿ ∈ TyVar 2 ]
      toRenameᵗ target-η-id Xᴿ ≡ toRenameᵗ source-η-empty Xᴸ
alias-chain-precise ()

alias-chain-representations : ∀ {Xᴸ : TyVar 0} {Xᴿ : TyVar 2}
  → toRenameᵗ source-η-empty Xᴸ ≡ toRenameᵗ target-η-id Xᴿ
  → μ₂ ⊢
      renameᵗ (toRenameᵗ source-η-empty)
        (lookupStore store-empty Xᴸ)
      ⊑ renameᵗ (toRenameᵗ target-η-id)
        (lookupStore alias-chain-target-store Xᴿ)
alias-chain-representations {()}

alias-chain-unmatched-targets : ∀ (Xᴿ : TyVar 2)
  → (∀ (Xᴸ : TyVar 0)
      → toRenameᵗ source-η-empty Xᴸ
        ≢ toRenameᵗ target-η-id Xᴿ)
  → lookupStore alias-chain-target-store Xᴿ ≡ ★
    ⊎ Σ[ Yᴿ ∈ TyVar 2 ]
        (lookupStore alias-chain-target-store Xᴿ ≡ ＇ Yᴿ)
      × (∀ (Xᴸ : TyVar 0)
          → toRenameᵗ source-η-empty Xᴸ
            ≢ toRenameᵗ target-η-id Yᴿ)
alias-chain-unmatched-targets Fin.zero unmatched =
  inj₂ (Fin.suc Fin.zero , refl , (λ ()))
alias-chain-unmatched-targets (Fin.suc Fin.zero) unmatched = inj₁ refl

alias-chain-world : World 0 2 2
alias-chain-world =
  world source-η-empty target-η-id μ₂ store-empty
    alias-chain-target-store alias-chain-precise
    alias-chain-representations alias-chain-unmatched-targets

alias-chain-rejects-strict :
  (∀ (Xᴿ : TyVar 2)
    → (∀ (Xᴸ : TyVar 0)
        → toRenameᵗ source-η-empty Xᴸ
          ≢ toRenameᵗ target-η-id Xᴿ)
    → lookupStore alias-chain-target-store Xᴿ ≡ ★)
  → ⊥
alias-chain-rejects-strict strict with strict Fin.zero (λ ())
alias-chain-rejects-strict strict | ()

d8a-W-precise :
  ∀ (Xᴸ : TyVar 1)
  → μ₂ (toRenameᵗ source-η-old Xᴸ) ≡ X⊑X
  → Σ[ Xᴿ ∈ TyVar 2 ]
      toRenameᵗ target-η-id Xᴿ ≡ toRenameᵗ source-η-old Xᴸ
d8a-W-precise Fin.zero precise = Fin.suc Fin.zero , refl

d8a-W-representations : ∀ {Xᴸ : TyVar 1} {Xᴿ : TyVar 2}
  → toRenameᵗ source-η-old Xᴸ ≡ toRenameᵗ target-η-id Xᴿ
  → μ₂ ⊢
      renameᵗ (toRenameᵗ source-η-old)
        (lookupStore d8a-source-store Xᴸ)
      ⊑ renameᵗ (toRenameᵗ target-η-id)
        (lookupStore d8a-target-store Xᴿ)
d8a-W-representations {Fin.zero} {Fin.zero} ()
d8a-W-representations {Fin.zero} {Fin.suc Fin.zero} refl = ι⊑ι

d8a-W-fresh-unmatched : ∀ (Xᴸ : TyVar 1)
  → toRenameᵗ source-η-old Xᴸ
      ≢ toRenameᵗ target-η-id Fin.zero
d8a-W-fresh-unmatched Fin.zero ()

d8a-W-violates-invariant4 :
  (∀ (Xᴿ : TyVar 2)
    → (∀ (Xᴸ : TyVar 1)
        → toRenameᵗ source-η-old Xᴸ
          ≢ toRenameᵗ target-η-id Xᴿ)
    → lookupStore d8a-target-store Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar 2 ]
          (lookupStore d8a-target-store Xᴿ ≡ ＇ Yᴿ)
        × (∀ (Xᴸ : TyVar 1)
            → toRenameᵗ source-η-old Xᴸ
              ≢ toRenameᵗ target-η-id Yᴿ))
  → ⊥
d8a-W-violates-invariant4 invariant
    with invariant Fin.zero d8a-W-fresh-unmatched
d8a-W-violates-invariant4 invariant | inj₁ ()
d8a-W-violates-invariant4 invariant | inj₂ (Yᴿ , () , Yᴿ-unmatched)

d8a-Wᵖ-precise :
  ∀ (Xᴸ : TyVar 1)
  → μ₂ (toRenameᵗ source-η-fresh Xᴸ) ≡ X⊑X
  → Σ[ Xᴿ ∈ TyVar 2 ]
      toRenameᵗ target-η-id Xᴿ ≡ toRenameᵗ source-η-fresh Xᴸ
d8a-Wᵖ-precise Fin.zero ()

d8a-Wᵖ-representations : ∀ {Xᴸ : TyVar 1} {Xᴿ : TyVar 2}
  → toRenameᵗ source-η-fresh Xᴸ ≡ toRenameᵗ target-η-id Xᴿ
  → μ₂ ⊢
      renameᵗ (toRenameᵗ source-η-fresh)
        (lookupStore d8a-source-store Xᴸ)
      ⊑ renameᵗ (toRenameᵗ target-η-id)
        (lookupStore d8a-target-store Xᴿ)
d8a-Wᵖ-representations {Fin.zero} {Fin.zero} refl = ι⊑ι
d8a-Wᵖ-representations {Fin.zero} {Fin.suc Fin.zero} ()

d8a-Wᵖ-old-unmatched : ∀ (Xᴸ : TyVar 1)
  → toRenameᵗ source-η-fresh Xᴸ
      ≢ toRenameᵗ target-η-id (Fin.suc Fin.zero)
d8a-Wᵖ-old-unmatched Fin.zero ()

d8a-Wᵖ-violates-invariant4 :
  (∀ (Xᴿ : TyVar 2)
    → (∀ (Xᴸ : TyVar 1)
        → toRenameᵗ source-η-fresh Xᴸ
          ≢ toRenameᵗ target-η-id Xᴿ)
    → lookupStore d8a-target-store Xᴿ ≡ ★
      ⊎ Σ[ Yᴿ ∈ TyVar 2 ]
          (lookupStore d8a-target-store Xᴿ ≡ ＇ Yᴿ)
        × (∀ (Xᴸ : TyVar 1)
            → toRenameᵗ source-η-fresh Xᴸ
              ≢ toRenameᵗ target-η-id Yᴿ))
  → ⊥
d8a-Wᵖ-violates-invariant4 invariant
    with invariant (Fin.suc Fin.zero) d8a-Wᵖ-old-unmatched
d8a-Wᵖ-violates-invariant4 invariant | inj₁ ()
d8a-Wᵖ-violates-invariant4 invariant | inj₂ (Yᴿ , () , Yᴿ-unmatched)

------------------------------------------------------------------------
-- T10 Probe 1 reconstruction: the same geometry with ★ representations
------------------------------------------------------------------------

t10-source-store : TyStore 1
t10-source-store = store-bind store-empty ★

t10-target-store : TyStore 2
t10-target-store = store-bind (store-bind store-empty ★) ★

t10-W-representations : ∀ {Xᴸ : TyVar 1} {Xᴿ : TyVar 2}
  → toRenameᵗ source-η-old Xᴸ ≡ toRenameᵗ target-η-id Xᴿ
  → μ₂ ⊢
      renameᵗ (toRenameᵗ source-η-old)
        (lookupStore t10-source-store Xᴸ)
      ⊑ renameᵗ (toRenameᵗ target-η-id)
        (lookupStore t10-target-store Xᴿ)
t10-W-representations {Fin.zero} {Fin.zero} ()
t10-W-representations {Fin.zero} {Fin.suc Fin.zero} refl = ★⊑★

t10-W-unmatched-targets : ∀ (Xᴿ : TyVar 2)
  → (∀ (Xᴸ : TyVar 1)
      → toRenameᵗ source-η-old Xᴸ
        ≢ toRenameᵗ target-η-id Xᴿ)
  → lookupStore t10-target-store Xᴿ ≡ ★
    ⊎ Σ[ Yᴿ ∈ TyVar 2 ]
        (lookupStore t10-target-store Xᴿ ≡ ＇ Yᴿ)
      × (∀ (Xᴸ : TyVar 1)
          → toRenameᵗ source-η-old Xᴸ
            ≢ toRenameᵗ target-η-id Yᴿ)
t10-W-unmatched-targets Fin.zero unmatched = inj₁ refl
t10-W-unmatched-targets (Fin.suc Fin.zero) unmatched =
  ⊥-elim (unmatched Fin.zero refl)

t10-W : World 1 2 2
t10-W =
  world source-η-old target-η-id μ₂ t10-source-store t10-target-store
    d8a-W-precise t10-W-representations t10-W-unmatched-targets

t10-Wᵖ-representations : ∀ {Xᴸ : TyVar 1} {Xᴿ : TyVar 2}
  → toRenameᵗ source-η-fresh Xᴸ ≡ toRenameᵗ target-η-id Xᴿ
  → μ₂ ⊢
      renameᵗ (toRenameᵗ source-η-fresh)
        (lookupStore t10-source-store Xᴸ)
      ⊑ renameᵗ (toRenameᵗ target-η-id)
        (lookupStore t10-target-store Xᴿ)
t10-Wᵖ-representations {Fin.zero} {Fin.zero} refl = ★⊑★
t10-Wᵖ-representations {Fin.zero} {Fin.suc Fin.zero} ()

t10-Wᵖ-unmatched-targets : ∀ (Xᴿ : TyVar 2)
  → (∀ (Xᴸ : TyVar 1)
      → toRenameᵗ source-η-fresh Xᴸ
        ≢ toRenameᵗ target-η-id Xᴿ)
  → lookupStore t10-target-store Xᴿ ≡ ★
    ⊎ Σ[ Yᴿ ∈ TyVar 2 ]
        (lookupStore t10-target-store Xᴿ ≡ ＇ Yᴿ)
      × (∀ (Xᴸ : TyVar 1)
          → toRenameᵗ source-η-fresh Xᴸ
            ≢ toRenameᵗ target-η-id Yᴿ)
t10-Wᵖ-unmatched-targets Fin.zero unmatched =
  ⊥-elim (unmatched Fin.zero refl)
t10-Wᵖ-unmatched-targets (Fin.suc Fin.zero) unmatched = inj₁ refl

t10-Wᵖ : World 1 2 2
t10-Wᵖ =
  world source-η-fresh target-η-id μ₂
    t10-source-store t10-target-store
    d8a-Wᵖ-precise t10-Wᵖ-representations t10-Wᵖ-unmatched-targets

t10-probe1-worlds-satisfy :
  RepresentationInvariant t10-W × RepresentationInvariant t10-Wᵖ
t10-probe1-worlds-satisfy =
  representationInvariant t10-W , representationInvariant t10-Wᵖ
