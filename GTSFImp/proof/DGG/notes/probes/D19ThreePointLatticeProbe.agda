module D19ThreePointLatticeProbe where

-- File Charter:
--   * Models D19 direction B with sandbox copies of marks, worlds, and the
--     variable-to-dynamic type-imprecision leaf; no live definition changes.
--   * Rescopes invariant (5) to the unannotated dynamic mark and requires the
--     paired-dynamic mark to have been formed by the paired-seal case.
--   * Checks the expanded YZ fixture with a paired-dynamic Z cell.
--   * Checks that ProjectionMismatch has no admissible widening-capable mark.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types using (TyCtx; Ty; TyVar; ★; ＇_; ‵_; `ℕ; renameᵗ)
open import TyStore using
  (TyStore; store-empty; store-bind; lookupStore)
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)


------------------------------------------------------------------------
-- Direction B sandbox
------------------------------------------------------------------------

data ThreePointMark : Set where
  X⊑X  : ThreePointMark
  X⊑★ᵖ : ThreePointMark
  X⊑★  : ThreePointMark

ThreePointEnv : TyCtx → Set
ThreePointEnv Δ = TyVar Δ → ThreePointMark

data CanWiden : ThreePointMark → Set where
  paired-widen      : CanWiden X⊑★ᵖ
  unannotated-widen : CanWiden X⊑★

infix 4 _⊢³_⊑_

data _⊢³_⊑_ {Δ : TyCtx} (μ : ThreePointEnv Δ)
    : Ty Δ → Ty Δ → Set where
  X⊑★-sandbox : ∀ {X}
    → CanWiden (μ X)
    → μ ⊢³ ＇ X ⊑ ★

-- This is history supplied by the sandbox fixture, not a reconstruction from
-- the two stores.  In particular, aligned direct ★/★ entries do not imply
-- paired-seal formation.

data CellFormation : Set where
  source-only-formation  : CellFormation
  paired-alias-formation : CellFormation
  paired-seal-formation  : CellFormation
  projection-formation   : CellFormation

data PairedSealFormed : CellFormation → Set where
  paired-seal-formed : PairedSealFormed paired-seal-formation

record ThreePointWorld (Δᴸ Δᴿ Δ : TyCtx) : Set where
  constructor three-point-world
  field
    ηᴸʷ : Δᴸ ↪ᵗ Δ
    ηᴿʷ : Δᴿ ↪ᵗ Δ
    impEnvʷ : ThreePointEnv Δ
    sourceStoreʷ : TyStore Δᴸ
    targetStoreʷ : TyStore Δᴿ
    formationʷ : TyVar Δ → CellFormation

open ThreePointWorld public

embedᴸ : ∀ {Δᴸ Δᴿ Δ}
  → ThreePointWorld Δᴸ Δᴿ Δ
  → Ty Δᴸ
  → Ty Δ
embedᴸ W = renameᵗ (toRenameᵗ (ηᴸʷ W))

embedᴿ : ∀ {Δᴸ Δᴿ Δ}
  → ThreePointWorld Δᴸ Δᴿ Δ
  → Ty Δᴿ
  → Ty Δ
embedᴿ W = renameᵗ (toRenameᵗ (ηᴿʷ W))

infix 4 _⊑³⟨_⟩_

_⊑³⟨_⟩_ : ∀ {Δᴸ Δᴿ Δ}
  → Ty Δᴸ
  → ThreePointWorld Δᴸ Δᴿ Δ
  → Ty Δᴿ
  → Set
A ⊑³⟨ W ⟩ B = impEnvʷ W ⊢³ embedᴸ W A ⊑ embedᴿ W B

-- Invariant (5) mentions only the unannotated X⊑★ point.  A source-★
-- cell carrying X⊑★ᵖ may therefore have an aligned target occupant.

RescopedInvariant5 : ∀ {Δᴸ Δᴿ Δ}
  → ThreePointWorld Δᴸ Δᴿ Δ
  → Set
RescopedInvariant5 {Δᴸ} {Δᴿ} W = ∀ (Xᴸ : TyVar Δᴸ)
  → impEnvʷ W (toRenameᵗ (ηᴸʷ W) Xᴸ) ≡ X⊑★
  → lookupStore (sourceStoreʷ W) Xᴸ ≡ ★
  → ∀ (Xᴿ : TyVar Δᴿ)
  → toRenameᵗ (ηᴿʷ W) Xᴿ ≢ toRenameᵗ (ηᴸʷ W) Xᴸ

-- Minting X⊑★ᵖ requires explicit paired-seal formation history.  Layout
-- facts such as alignment and direct ★/★ entries are intentionally absent.

PairedMarkMintingDiscipline : ∀ {Δᴸ Δᴿ Δ}
  → ThreePointWorld Δᴸ Δᴿ Δ
  → Set
PairedMarkMintingDiscipline W = ∀ Z
  → impEnvʷ W Z ≡ X⊑★ᵖ
  → PairedSealFormed (formationʷ W Z)

Admissible : ∀ {Δᴸ Δᴿ Δ}
  → ThreePointWorld Δᴸ Δᴿ Δ
  → Set
Admissible W = RescopedInvariant5 W × PairedMarkMintingDiscipline W


------------------------------------------------------------------------
-- Inlined YZ fixture
------------------------------------------------------------------------

yz-source-store : TyStore 3
yz-source-store =
  store-bind (store-bind (store-bind store-empty ★) (＇ Fin.zero)) (‵ `ℕ)

yz-target-store : TyStore 2
yz-target-store = store-bind (store-bind store-empty ★) (＇ Fin.zero)

yz-source-η : 3 ↪ᵗ 3
yz-source-η = keep (keep (keep empty))

yz-target-η : 2 ↪ᵗ 3
yz-target-η = skip (keep (keep empty))

yz-env : ThreePointEnv 3
yz-env Fin.zero = X⊑★
yz-env (Fin.suc Fin.zero) = X⊑★
yz-env (Fin.suc (Fin.suc Fin.zero)) = X⊑★ᵖ

yz-formation : TyVar 3 → CellFormation
yz-formation Fin.zero = source-only-formation
yz-formation (Fin.suc Fin.zero) = paired-alias-formation
yz-formation (Fin.suc (Fin.suc Fin.zero)) = paired-seal-formation

yz-world : ThreePointWorld 3 2 3
yz-world =
  three-point-world yz-source-η yz-target-η yz-env
    yz-source-store yz-target-store yz-formation

yz-rescoped-invariant5 : RescopedInvariant5 yz-world
yz-rescoped-invariant5 Fin.zero refl () Xᴿ
yz-rescoped-invariant5 (Fin.suc Fin.zero) refl () Xᴿ
yz-rescoped-invariant5 (Fin.suc (Fin.suc Fin.zero)) () entry Xᴿ

yz-paired-mark-minted : PairedMarkMintingDiscipline yz-world
yz-paired-mark-minted Fin.zero ()
yz-paired-mark-minted (Fin.suc Fin.zero) ()
yz-paired-mark-minted (Fin.suc (Fin.suc Fin.zero)) refl =
  paired-seal-formed

yz-admissible : Admissible yz-world
yz-admissible = yz-rescoped-invariant5 , yz-paired-mark-minted

-- This is the live relation's variable-to-dynamic leaf, copied with CanWiden
-- as its sole mark change.  The paired Z point still licenses the needed leaf.

yz-Z-to-star :
  (＇ (Fin.suc (Fin.suc Fin.zero))) ⊑³⟨ yz-world ⟩ ★
yz-Z-to-star = X⊑★-sandbox paired-widen


------------------------------------------------------------------------
-- Inlined ProjectionMismatch fixture
------------------------------------------------------------------------

projection-mismatch-store : TyStore 1
projection-mismatch-store = store-bind store-empty ★

projection-mismatch-env : ThreePointMark → ThreePointEnv 1
projection-mismatch-env mark Fin.zero = mark

projection-mismatch-formation : TyVar 1 → CellFormation
projection-mismatch-formation Fin.zero = projection-formation

projection-mismatch-world : ThreePointMark → ThreePointWorld 1 1 1
projection-mismatch-world mark =
  three-point-world (keep empty) (keep empty)
    (projection-mismatch-env mark)
    projection-mismatch-store projection-mismatch-store
    projection-mismatch-formation

projection-paired-world : ThreePointWorld 1 1 1
projection-paired-world = projection-mismatch-world X⊑★ᵖ

projection-unannotated-world : ThreePointWorld 1 1 1
projection-unannotated-world = projection-mismatch-world X⊑★

projection-not-paired-seal-formed :
  PairedSealFormed projection-formation → ⊥
projection-not-paired-seal-formed ()

projection-paired-cannot-be-minted :
  PairedMarkMintingDiscipline projection-paired-world → ⊥
projection-paired-cannot-be-minted discipline =
  projection-not-paired-seal-formed (discipline Fin.zero refl)

projection-unannotated-rejected-by-invariant5 :
  RescopedInvariant5 projection-unannotated-world → ⊥
projection-unannotated-rejected-by-invariant5 invariant5 =
  invariant5 Fin.zero refl refl Fin.zero refl

-- These are the only two marks with CanWiden evidence.  The unannotated case
-- violates rescoped (5); the paired case violates the minting discipline.

projection-mismatch-still-rejected : ∀ {mark}
  → CanWiden mark
  → Admissible (projection-mismatch-world mark)
  → ⊥
projection-mismatch-still-rejected unannotated-widen
    (invariant5 , minting) =
  projection-unannotated-rejected-by-invariant5 invariant5
projection-mismatch-still-rejected paired-widen (invariant5 , minting) =
  projection-paired-cannot-be-minted minting
