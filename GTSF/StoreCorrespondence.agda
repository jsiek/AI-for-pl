module StoreCorrespondence where

-- File Charter:
--   * Separate-store replacement core for the old shared `StoreNrw` encoding.
--   * Defines explicit left/right seal correspondence entries and projections
--     to the left and right runtime stores.
--   * Provides a compatibility embedding from the existing shared `StoreNrw`
--     so proofs can be migrated one surface at a time.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import Types
open import Store using (StoreWfAt)
open import Coercions
open import NarrowWiden using
  ( StoreNrw
  ; _꞉_
  ; _꞉=_⊒
  ; ⊒_꞉=☆
  ; srcStoreⁿ
  ; tgtStoreⁿ
  )
import proof.Core.Properties.NarrowWidenStoreInvariantDef as NWStore
open import proof.Core.Properties.NarrowWidenStoreInvariantDef
  using (StoreDetWf)
import proof.Core.Properties.NarrowWidenStoreInvariantProof as NWStoreProof

------------------------------------------------------------------------
-- Explicit seal correspondence
------------------------------------------------------------------------

data SealCorrEntry : Set where
  matched : TyVar → Ty → TyVar → Ty → SealCorrEntry
  left-only : TyVar → Ty → SealCorrEntry
  right-only : TyVar → Ty → SealCorrEntry

SealCorr : Set
SealCorr = List SealCorrEntry

leftStoreEntry : SealCorrEntry → Store → Store
leftStoreEntry (matched α A β B) Σ = (α , A) ∷ Σ
leftStoreEntry (left-only α A) Σ = (α , A) ∷ Σ
leftStoreEntry (right-only β B) Σ = Σ

rightStoreEntry : SealCorrEntry → Store → Store
rightStoreEntry (matched α A β B) Σ = (β , B) ∷ Σ
rightStoreEntry (left-only α A) Σ = Σ
rightStoreEntry (right-only β B) Σ = (β , B) ∷ Σ

leftStore : SealCorr → Store
leftStore [] = []
leftStore (entry ∷ ρ) = leftStoreEntry entry (leftStore ρ)

rightStore : SealCorr → Store
rightStore [] = []
rightStore (entry ∷ ρ) = rightStoreEntry entry (rightStore ρ)

shiftSealCorrEntry : SealCorrEntry → SealCorrEntry
shiftSealCorrEntry (matched α A β B) =
  matched (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B)
shiftSealCorrEntry (left-only α A) = left-only (suc α) (⇑ᵗ A)
shiftSealCorrEntry (right-only β B) = right-only (suc β) (⇑ᵗ B)

⇑ᶜorr : SealCorr → SealCorr
⇑ᶜorr = map shiftSealCorrEntry

shiftLeftSealCorrEntry : SealCorrEntry → SealCorrEntry
shiftLeftSealCorrEntry (matched α A β B) =
  matched (suc α) (⇑ᵗ A) β B
shiftLeftSealCorrEntry (left-only α A) = left-only (suc α) (⇑ᵗ A)
shiftLeftSealCorrEntry (right-only β B) = right-only β B

⇑ˡᶜorr : SealCorr → SealCorr
⇑ˡᶜorr = map shiftLeftSealCorrEntry

shiftRightSealCorrEntry : SealCorrEntry → SealCorrEntry
shiftRightSealCorrEntry (matched α A β B) =
  matched α A (suc β) (⇑ᵗ B)
shiftRightSealCorrEntry (left-only α A) = left-only α A
shiftRightSealCorrEntry (right-only β B) = right-only (suc β) (⇑ᵗ B)

⇑ʳᶜorr : SealCorr → SealCorr
⇑ʳᶜorr = map shiftRightSealCorrEntry

-- Well-scoped correspondence
------------------------------------------------------------------------

record StoreCorr (ΔL ΔR : TyCtx) (ρ : SealCorr) : Set₁ where
  constructor store-corr
  field
    leftStore-det : StoreDetWf ΔL (leftStore ρ)
    rightStore-det : StoreDetWf ΔR (rightStore ρ)

open StoreCorr public

corr-nil : ∀ {ΔL ΔR} →
  StoreCorr ΔL ΔR []
corr-nil =
  store-corr
    (record
      { at = record { bound = λ (); wfTy = λ () }
      ; wfOlder = λ ()
      ; unique = λ ()
      })
    (record
      { at = record { bound = λ (); wfTy = λ () }
      ; wfOlder = λ ()
      ; unique = λ ()
      })

corr-matched : ∀ {ΔL ΔR ρ α β A B} →
  α < ΔL →
  β < ΔR →
  WfTy ΔL A →
  WfTy ΔR B →
  WfTy α A →
  WfTy β B →
  (∀ {C} → (α , C) ∈ leftStore ρ → A ≡ C) →
  (∀ {D} → (β , D) ∈ rightStore ρ → B ≡ D) →
  StoreCorr ΔL ΔR ρ →
    -----------------------------------------
  StoreCorr ΔL ΔR (matched α A β B ∷ ρ)
corr-matched α< β< hA hB hA-old hB-old left-unique right-unique corr =
  store-corr
    (record
      { at =
          record
            { bound = λ
                { (here refl) → α<
                ; (there α∈ρ) →
                    StoreWfAt.bound
                      (NWStore.StoreDetWf.at (leftStore-det corr)) α∈ρ
                }
            ; wfTy = λ
                { (here refl) → hA
                ; (there α∈ρ) →
                    StoreWfAt.wfTy
                      (NWStore.StoreDetWf.at (leftStore-det corr)) α∈ρ
                }
            }
      ; wfOlder = λ
          { (here refl) → hA-old
          ; (there α∈ρ) →
              NWStore.StoreDetWf.wfOlder (leftStore-det corr) α∈ρ
          }
      ; unique = λ
          { (here refl) (here refl) → refl
          ; (here refl) (there α∈ρ) → left-unique α∈ρ
          ; (there α∈ρ) (here refl) → sym (left-unique α∈ρ)
          ; (there α∈ρ) (there α∈ρ′) →
              NWStore.StoreDetWf.unique (leftStore-det corr) α∈ρ α∈ρ′
          }
      })
    (record
      { at =
          record
            { bound = λ
                { (here refl) → β<
                ; (there β∈ρ) →
                    StoreWfAt.bound
                      (NWStore.StoreDetWf.at (rightStore-det corr)) β∈ρ
                }
            ; wfTy = λ
                { (here refl) → hB
                ; (there β∈ρ) →
                    StoreWfAt.wfTy
                      (NWStore.StoreDetWf.at (rightStore-det corr)) β∈ρ
                }
            }
      ; wfOlder = λ
          { (here refl) → hB-old
          ; (there β∈ρ) →
              NWStore.StoreDetWf.wfOlder (rightStore-det corr) β∈ρ
          }
      ; unique = λ
          { (here refl) (here refl) → refl
          ; (here refl) (there β∈ρ) → right-unique β∈ρ
          ; (there β∈ρ) (here refl) → sym (right-unique β∈ρ)
          ; (there β∈ρ) (there β∈ρ′) →
              NWStore.StoreDetWf.unique (rightStore-det corr) β∈ρ β∈ρ′
          }
      })

corr-left : ∀ {ΔL ΔR ρ α A} →
  α < ΔL →
  WfTy ΔL A →
  WfTy α A →
  (∀ {C} → (α , C) ∈ leftStore ρ → A ≡ C) →
  StoreCorr ΔL ΔR ρ →
    ------------------------------------
  StoreCorr ΔL ΔR (left-only α A ∷ ρ)
corr-left α< hA hA-old left-unique corr =
  store-corr
    (record
      { at =
          record
            { bound = λ
                { (here refl) → α<
                ; (there α∈ρ) →
                    StoreWfAt.bound
                      (NWStore.StoreDetWf.at (leftStore-det corr)) α∈ρ
                }
            ; wfTy = λ
                { (here refl) → hA
                ; (there α∈ρ) →
                    StoreWfAt.wfTy
                      (NWStore.StoreDetWf.at (leftStore-det corr)) α∈ρ
                }
            }
      ; wfOlder = λ
          { (here refl) → hA-old
          ; (there α∈ρ) →
              NWStore.StoreDetWf.wfOlder (leftStore-det corr) α∈ρ
          }
      ; unique = λ
          { (here refl) (here refl) → refl
          ; (here refl) (there α∈ρ) → left-unique α∈ρ
          ; (there α∈ρ) (here refl) → sym (left-unique α∈ρ)
          ; (there α∈ρ) (there α∈ρ′) →
              NWStore.StoreDetWf.unique (leftStore-det corr) α∈ρ α∈ρ′
          }
      })
    (rightStore-det corr)

corr-right : ∀ {ΔL ΔR ρ β B} →
  β < ΔR →
  WfTy ΔR B →
  WfTy β B →
  (∀ {D} → (β , D) ∈ rightStore ρ → B ≡ D) →
  StoreCorr ΔL ΔR ρ →
    -------------------------------------
  StoreCorr ΔL ΔR (right-only β B ∷ ρ)
corr-right β< hB hB-old right-unique corr =
  store-corr
    (leftStore-det corr)
    (record
      { at =
          record
            { bound = λ
                { (here refl) → β<
                ; (there β∈ρ) →
                    StoreWfAt.bound
                      (NWStore.StoreDetWf.at (rightStore-det corr)) β∈ρ
                }
            ; wfTy = λ
                { (here refl) → hB
                ; (there β∈ρ) →
                    StoreWfAt.wfTy
                      (NWStore.StoreDetWf.at (rightStore-det corr)) β∈ρ
                }
            }
      ; wfOlder = λ
          { (here refl) → hB-old
          ; (there β∈ρ) →
              NWStore.StoreDetWf.wfOlder (rightStore-det corr) β∈ρ
          }
      ; unique = λ
          { (here refl) (here refl) → refl
          ; (here refl) (there β∈ρ) → right-unique β∈ρ
          ; (there β∈ρ) (here refl) → sym (right-unique β∈ρ)
          ; (there β∈ρ) (there β∈ρ′) →
              NWStore.StoreDetWf.unique (rightStore-det corr) β∈ρ β∈ρ′
          }
      })

leftStore-wf :
  ∀ {ΔL ΔR ρ} →
  StoreCorr ΔL ΔR ρ →
  StoreWfAt ΔL (leftStore ρ)
leftStore-wf corr = NWStore.StoreDetWf.at (leftStore-det corr)

rightStore-wf :
  ∀ {ΔL ΔR ρ} →
  StoreCorr ΔL ΔR ρ →
  StoreWfAt ΔR (rightStore ρ)
rightStore-wf corr = NWStore.StoreDetWf.at (rightStore-det corr)

------------------------------------------------------------------------
-- Compatibility with the old shared representation
------------------------------------------------------------------------

fromStoreNrw : StoreNrw → SealCorr
fromStoreNrw [] = []
fromStoreNrw ((α ꞉ p) ∷ σ) =
  matched α (src p) α (tgt p) ∷ fromStoreNrw σ
fromStoreNrw ((α ꞉= A ⊒) ∷ σ) = right-only α A ∷ fromStoreNrw σ
fromStoreNrw ((⊒ α ꞉=☆) ∷ σ) = left-only α ★ ∷ fromStoreNrw σ

leftStore-fromStoreNrw :
  ∀ σ →
  leftStore (fromStoreNrw σ) ≡ srcStoreⁿ σ
leftStore-fromStoreNrw [] = refl
leftStore-fromStoreNrw ((α ꞉ p) ∷ σ) =
  cong ((α , src p) ∷_) (leftStore-fromStoreNrw σ)
leftStore-fromStoreNrw ((α ꞉= A ⊒) ∷ σ) =
  leftStore-fromStoreNrw σ
leftStore-fromStoreNrw ((⊒ α ꞉=☆) ∷ σ) =
  cong ((α , ★) ∷_) (leftStore-fromStoreNrw σ)

rightStore-fromStoreNrw :
  ∀ σ →
  rightStore (fromStoreNrw σ) ≡ tgtStoreⁿ σ
rightStore-fromStoreNrw [] = refl
rightStore-fromStoreNrw ((α ꞉ p) ∷ σ) =
  cong ((α , tgt p) ∷_) (rightStore-fromStoreNrw σ)
rightStore-fromStoreNrw ((α ꞉= A ⊒) ∷ σ) =
  cong ((α , A) ∷_) (rightStore-fromStoreNrw σ)
rightStore-fromStoreNrw ((⊒ α ꞉=☆) ∷ σ) =
  rightStore-fromStoreNrw σ

leftStore-⇑ᶜorr :
  ∀ ρ →
  leftStore (⇑ᶜorr ρ) ≡ ⟰ᵗ (leftStore ρ)
leftStore-⇑ᶜorr [] = refl
leftStore-⇑ᶜorr (matched α A β B ∷ ρ) =
  cong ((suc α , ⇑ᵗ A) ∷_) (leftStore-⇑ᶜorr ρ)
leftStore-⇑ᶜorr (left-only α A ∷ ρ) =
  cong ((suc α , ⇑ᵗ A) ∷_) (leftStore-⇑ᶜorr ρ)
leftStore-⇑ᶜorr (right-only β B ∷ ρ) =
  leftStore-⇑ᶜorr ρ

rightStore-⇑ᶜorr :
  ∀ ρ →
  rightStore (⇑ᶜorr ρ) ≡ ⟰ᵗ (rightStore ρ)
rightStore-⇑ᶜorr [] = refl
rightStore-⇑ᶜorr (matched α A β B ∷ ρ) =
  cong ((suc β , ⇑ᵗ B) ∷_) (rightStore-⇑ᶜorr ρ)
rightStore-⇑ᶜorr (left-only α A ∷ ρ) =
  rightStore-⇑ᶜorr ρ
rightStore-⇑ᶜorr (right-only β B ∷ ρ) =
  cong ((suc β , ⇑ᵗ B) ∷_) (rightStore-⇑ᶜorr ρ)

leftStore-⇑ˡᶜorr :
  ∀ ρ →
  leftStore (⇑ˡᶜorr ρ) ≡ ⟰ᵗ (leftStore ρ)
leftStore-⇑ˡᶜorr [] = refl
leftStore-⇑ˡᶜorr (matched α A β B ∷ ρ) =
  cong ((suc α , ⇑ᵗ A) ∷_) (leftStore-⇑ˡᶜorr ρ)
leftStore-⇑ˡᶜorr (left-only α A ∷ ρ) =
  cong ((suc α , ⇑ᵗ A) ∷_) (leftStore-⇑ˡᶜorr ρ)
leftStore-⇑ˡᶜorr (right-only β B ∷ ρ) =
  leftStore-⇑ˡᶜorr ρ

rightStore-⇑ˡᶜorr :
  ∀ ρ →
  rightStore (⇑ˡᶜorr ρ) ≡ rightStore ρ
rightStore-⇑ˡᶜorr [] = refl
rightStore-⇑ˡᶜorr (matched α A β B ∷ ρ) =
  cong ((β , B) ∷_) (rightStore-⇑ˡᶜorr ρ)
rightStore-⇑ˡᶜorr (left-only α A ∷ ρ) =
  rightStore-⇑ˡᶜorr ρ
rightStore-⇑ˡᶜorr (right-only β B ∷ ρ) =
  cong ((β , B) ∷_) (rightStore-⇑ˡᶜorr ρ)

leftStore-⇑ʳᶜorr :
  ∀ ρ →
  leftStore (⇑ʳᶜorr ρ) ≡ leftStore ρ
leftStore-⇑ʳᶜorr [] = refl
leftStore-⇑ʳᶜorr (matched α A β B ∷ ρ) =
  cong ((α , A) ∷_) (leftStore-⇑ʳᶜorr ρ)
leftStore-⇑ʳᶜorr (left-only α A ∷ ρ) =
  cong ((α , A) ∷_) (leftStore-⇑ʳᶜorr ρ)
leftStore-⇑ʳᶜorr (right-only β B ∷ ρ) =
  leftStore-⇑ʳᶜorr ρ

rightStore-⇑ʳᶜorr :
  ∀ ρ →
  rightStore (⇑ʳᶜorr ρ) ≡ ⟰ᵗ (rightStore ρ)
rightStore-⇑ʳᶜorr [] = refl
rightStore-⇑ʳᶜorr (matched α A β B ∷ ρ) =
  cong ((suc β , ⇑ᵗ B) ∷_) (rightStore-⇑ʳᶜorr ρ)
rightStore-⇑ʳᶜorr (left-only α A ∷ ρ) =
  rightStore-⇑ʳᶜorr ρ
rightStore-⇑ʳᶜorr (right-only β B ∷ ρ) =
  cong ((suc β , ⇑ᵗ B) ∷_) (rightStore-⇑ʳᶜorr ρ)

leftStore-⇑ˡᶜorr-zero∉ :
  ∀ {ρ A} →
  (zero , A) ∈ leftStore (⇑ˡᶜorr ρ) →
  ⊥
leftStore-⇑ˡᶜorr-zero∉ {ρ = []} ()
leftStore-⇑ˡᶜorr-zero∉ {ρ = matched α A β B ∷ ρ} (here ())
leftStore-⇑ˡᶜorr-zero∉ {ρ = matched α A β B ∷ ρ} (there h) =
  leftStore-⇑ˡᶜorr-zero∉ {ρ = ρ} h
leftStore-⇑ˡᶜorr-zero∉ {ρ = left-only α A ∷ ρ} (here ())
leftStore-⇑ˡᶜorr-zero∉ {ρ = left-only α A ∷ ρ} (there h) =
  leftStore-⇑ˡᶜorr-zero∉ {ρ = ρ} h
leftStore-⇑ˡᶜorr-zero∉ {ρ = right-only β B ∷ ρ} h =
  leftStore-⇑ˡᶜorr-zero∉ {ρ = ρ} h

rightStore-⇑ʳᶜorr-zero∉ :
  ∀ {ρ A} →
  (zero , A) ∈ rightStore (⇑ʳᶜorr ρ) →
  ⊥
rightStore-⇑ʳᶜorr-zero∉ {ρ = []} ()
rightStore-⇑ʳᶜorr-zero∉ {ρ = matched α A β B ∷ ρ} (here ())
rightStore-⇑ʳᶜorr-zero∉ {ρ = matched α A β B ∷ ρ} (there h) =
  rightStore-⇑ʳᶜorr-zero∉ {ρ = ρ} h
rightStore-⇑ʳᶜorr-zero∉ {ρ = left-only α A ∷ ρ} h =
  rightStore-⇑ʳᶜorr-zero∉ {ρ = ρ} h
rightStore-⇑ʳᶜorr-zero∉ {ρ = right-only β B ∷ ρ} (here ())
rightStore-⇑ʳᶜorr-zero∉ {ρ = right-only β B ∷ ρ} (there h) =
  rightStore-⇑ʳᶜorr-zero∉ {ρ = ρ} h

corr-⇑ᶜorr :
  ∀ {ΔL ΔR ρ} →
  StoreCorr ΔL ΔR ρ →
  StoreCorr (suc ΔL) (suc ΔR) (⇑ᶜorr ρ)
corr-⇑ᶜorr {ρ = ρ} corr =
  store-corr
    (subst
      (λ Σ → StoreDetWf _ Σ)
      (sym (leftStore-⇑ᶜorr ρ))
      (NWStoreProof.StoreDetWf-⟰ᵗ (leftStore-det corr)))
    (subst
      (λ Σ → StoreDetWf _ Σ)
      (sym (rightStore-⇑ᶜorr ρ))
      (NWStoreProof.StoreDetWf-⟰ᵗ (rightStore-det corr)))

corr-⇑ˡᶜorr :
  ∀ {ΔL ΔR ρ} →
  StoreCorr ΔL ΔR ρ →
  StoreCorr (suc ΔL) ΔR (⇑ˡᶜorr ρ)
corr-⇑ˡᶜorr {ρ = ρ} corr =
  store-corr
    (subst
      (λ Σ → StoreDetWf _ Σ)
      (sym (leftStore-⇑ˡᶜorr ρ))
      (NWStoreProof.StoreDetWf-⟰ᵗ (leftStore-det corr)))
    (subst
      (λ Σ → StoreDetWf _ Σ)
      (sym (rightStore-⇑ˡᶜorr ρ))
      (rightStore-det corr))

corr-⇑ʳᶜorr :
  ∀ {ΔL ΔR ρ} →
  StoreCorr ΔL ΔR ρ →
  StoreCorr ΔL (suc ΔR) (⇑ʳᶜorr ρ)
corr-⇑ʳᶜorr {ρ = ρ} corr =
  store-corr
    (subst
      (λ Σ → StoreDetWf _ Σ)
      (sym (leftStore-⇑ʳᶜorr ρ))
      (leftStore-det corr))
    (subst
      (λ Σ → StoreDetWf _ Σ)
      (sym (rightStore-⇑ʳᶜorr ρ))
      (NWStoreProof.StoreDetWf-⟰ᵗ (rightStore-det corr)))
