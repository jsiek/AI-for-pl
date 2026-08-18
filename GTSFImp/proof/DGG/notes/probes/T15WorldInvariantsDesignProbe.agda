module T15WorldInvariantsDesignProbe where

-- File Charter:
--   * Type-checks the D16 seven-field World record and empty-store
--     initialWorld draft without changing the live relation.
--   * Reconstructs the D8a and T10 Probe 1 rebase worlds and checks whether
--     their representation pairs satisfy the drafted invariant.
--   * Contains no implementation of the World migration.

open import Data.Empty using (⊥)
import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (TyCtx; Ty; TyVar; ★; ＇_; ‵_; `ℕ; renameᵗ)
open import TyStore using (TyStore; store-empty; store-lift; store-bind)
open import Consistency using (_↪ᵗ_; empty; keep; skip; id↪ᵗ; toRenameᵗ)
open import Imprecision using
  (ImpEnv; X⊑X; X⊑★; extendᵐ; instᵐ; _⊢_⊑_; ★⊑★; ι⊑ι)
open import proof.ImprecisionConsistency using
  (refl⊑; toRenameᵗ-injective)
open import proof.DGG.CastTermImprecision2 using (resolveRep)

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
            (resolveRep sourceStoreʷ (＇ Xᴸ))
          ⊑ renameᵗ (toRenameᵗ ηᴿʷ)
            (resolveRep targetStoreʷ (＇ Xᴿ))

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
        (resolveRep (sourceStoreʷ W) (＇ Xᴸ))
      ⊑ renameᵗ (toRenameᵗ (ηᴿʷ W))
        (resolveRep (targetStoreʷ W) (＇ Xᴿ))

representationInvariant : ∀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
  → RepresentationInvariant W
representationInvariant W = representationsImpreciseʷ W

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
        (resolveRep (emptyStore Δ) (＇ Xᴸ))
      ⊑ renameᵗ (toRenameᵗ id↪ᵗ)
        (resolveRep (emptyStore Δ) (＇ Xᴿ))
initialRepresentations {Xᴸ = Xᴸ} aligned
    with toRenameᵗ-injective id↪ᵗ aligned
initialRepresentations {Xᴸ = Xᴸ} aligned | refl = refl⊑ _

initialWorld : ∀ {Δ} → ImpEnv Δ → World Δ Δ Δ
initialWorld {Δ} μ =
  world id↪ᵗ id↪ᵗ μ (emptyStore Δ) (emptyStore Δ)
    (λ Xᴸ precise → Xᴸ , refl)
    initialRepresentations

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
-- D8a reconstruction: both rebase endpoints satisfy the invariant
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

ℕ₀ : Ty 0
ℕ₀ = ‵ `ℕ

ℕ₁ : Ty 1
ℕ₁ = ‵ `ℕ

d8a-source-store : TyStore 1
d8a-source-store = store-bind store-empty ℕ₀

d8a-target-store : TyStore 2
d8a-target-store = store-bind (store-bind store-empty ℕ₀) ℕ₁

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
        (resolveRep d8a-source-store (＇ Xᴸ))
      ⊑ renameᵗ (toRenameᵗ target-η-id)
        (resolveRep d8a-target-store (＇ Xᴿ))
d8a-W-representations {Fin.zero} {Fin.zero} ()
d8a-W-representations {Fin.zero} {Fin.suc Fin.zero} refl = ι⊑ι

d8a-W : World 1 2 2
d8a-W =
  world source-η-old target-η-id μ₂ d8a-source-store d8a-target-store
    d8a-W-precise d8a-W-representations

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
        (resolveRep d8a-source-store (＇ Xᴸ))
      ⊑ renameᵗ (toRenameᵗ target-η-id)
        (resolveRep d8a-target-store (＇ Xᴿ))
d8a-Wᵖ-representations {Fin.zero} {Fin.zero} refl = ι⊑ι
d8a-Wᵖ-representations {Fin.zero} {Fin.suc Fin.zero} ()

d8a-Wᵖ : World 1 2 2
d8a-Wᵖ =
  world source-η-fresh target-η-id μ₂
    d8a-source-store d8a-target-store
    d8a-Wᵖ-precise d8a-Wᵖ-representations

d8a-refuting-worlds-satisfy :
  RepresentationInvariant d8a-W × RepresentationInvariant d8a-Wᵖ
d8a-refuting-worlds-satisfy =
  representationInvariant d8a-W , representationInvariant d8a-Wᵖ

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
        (resolveRep t10-source-store (＇ Xᴸ))
      ⊑ renameᵗ (toRenameᵗ target-η-id)
        (resolveRep t10-target-store (＇ Xᴿ))
t10-W-representations {Fin.zero} {Fin.zero} ()
t10-W-representations {Fin.zero} {Fin.suc Fin.zero} refl = ★⊑★

t10-W : World 1 2 2
t10-W =
  world source-η-old target-η-id μ₂ t10-source-store t10-target-store
    d8a-W-precise t10-W-representations

t10-Wᵖ-representations : ∀ {Xᴸ : TyVar 1} {Xᴿ : TyVar 2}
  → toRenameᵗ source-η-fresh Xᴸ ≡ toRenameᵗ target-η-id Xᴿ
  → μ₂ ⊢
      renameᵗ (toRenameᵗ source-η-fresh)
        (resolveRep t10-source-store (＇ Xᴸ))
      ⊑ renameᵗ (toRenameᵗ target-η-id)
        (resolveRep t10-target-store (＇ Xᴿ))
t10-Wᵖ-representations {Fin.zero} {Fin.zero} refl = ★⊑★
t10-Wᵖ-representations {Fin.zero} {Fin.suc Fin.zero} ()

t10-Wᵖ : World 1 2 2
t10-Wᵖ =
  world source-η-fresh target-η-id μ₂
    t10-source-store t10-target-store
    d8a-Wᵖ-precise t10-Wᵖ-representations

t10-probe1-worlds-satisfy :
  RepresentationInvariant t10-W × RepresentationInvariant t10-Wᵖ
t10-probe1-worlds-satisfy =
  representationInvariant t10-W , representationInvariant t10-Wᵖ

