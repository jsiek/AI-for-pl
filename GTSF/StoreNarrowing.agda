module StoreNarrowing where

-- File Charter:
--   * Prototype replacement shape for `StoreCorrespondence.StoreCorr`.
--   * Defines a separate-namespace store narrowing context matching the
--     store-only `σ` fragment of POPL 2027 Fig. 12.
--   * The `StoreNarrowing` judgment itself carries the payload narrowing,
--     payload well-formedness, namespace mediation, and no-duplicate-seal
--     invariants needed by term narrowing.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym)

open import Types
open import Store using (StoreWfAt)
open import Coercions
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import Mediation using (MedTy; VarCorr)
import proof.NarrowWidenProperties as NWP
open import proof.NarrowWidenProperties using (StoreDetWf)

------------------------------------------------------------------------
-- Store narrowing entries
------------------------------------------------------------------------

infix 6 _꞉_꞉_⦂_ _꞉=_⊒ ⊒_꞉=☆

data StoreNarrowingEntry : Set where
  _꞉_꞉_⦂_ : TyVar → Coercion → TyVar → Ty → StoreNarrowingEntry
  _꞉=_⊒ : TyVar → Ty → StoreNarrowingEntry
  ⊒_꞉=☆ : TyVar → StoreNarrowingEntry

StoreNarrowingCtx : Set
StoreNarrowingCtx = List StoreNarrowingEntry

leftStoreEntry : StoreNarrowingEntry → Store → Store
leftStoreEntry (α ꞉ p ꞉ β ⦂ B) Σ = (α , src p) ∷ Σ
leftStoreEntry (β ꞉= B ⊒) Σ = Σ
leftStoreEntry (⊒ α ꞉=☆) Σ = (α , ★) ∷ Σ

rightStoreEntry : StoreNarrowingEntry → Store → Store
rightStoreEntry (α ꞉ p ꞉ β ⦂ B) Σ = (β , B) ∷ Σ
rightStoreEntry (β ꞉= B ⊒) Σ = (β , B) ∷ Σ
rightStoreEntry (⊒ α ꞉=☆) Σ = Σ

leftStore : StoreNarrowingCtx → Store
leftStore [] = []
leftStore (entry ∷ σ) = leftStoreEntry entry (leftStore σ)

rightStore : StoreNarrowingCtx → Store
rightStore [] = []
rightStore (entry ∷ σ) = rightStoreEntry entry (rightStore σ)

NoStoreEntry : TyVar → Store → Set
NoStoreEntry α Σ = ∀ {A} → (α , A) ∈ Σ → ⊥

shiftStoreNarrowingEntry : StoreNarrowingEntry → StoreNarrowingEntry
shiftStoreNarrowingEntry (α ꞉ p ꞉ β ⦂ B) =
  suc α ꞉ ⇑ᶜ p ꞉ suc β ⦂ ⇑ᵗ B
shiftStoreNarrowingEntry (β ꞉= B ⊒) = suc β ꞉= ⇑ᵗ B ⊒
shiftStoreNarrowingEntry (⊒ α ꞉=☆) = ⊒ suc α ꞉=☆

⇑ˢ : StoreNarrowingCtx → StoreNarrowingCtx
⇑ˢ = map shiftStoreNarrowingEntry

shiftLeftStoreNarrowingEntry : StoreNarrowingEntry → StoreNarrowingEntry
shiftLeftStoreNarrowingEntry (α ꞉ p ꞉ β ⦂ B) =
  suc α ꞉ ⇑ᶜ p ꞉ β ⦂ B
shiftLeftStoreNarrowingEntry (β ꞉= B ⊒) = β ꞉= B ⊒
shiftLeftStoreNarrowingEntry (⊒ α ꞉=☆) = ⊒ suc α ꞉=☆

⇑ˡˢ : StoreNarrowingCtx → StoreNarrowingCtx
⇑ˡˢ = map shiftLeftStoreNarrowingEntry

shiftRightStoreNarrowingEntry : StoreNarrowingEntry → StoreNarrowingEntry
shiftRightStoreNarrowingEntry (α ꞉ p ꞉ β ⦂ B) =
  α ꞉ p ꞉ suc β ⦂ ⇑ᵗ B
shiftRightStoreNarrowingEntry (β ꞉= B ⊒) = suc β ꞉= ⇑ᵗ B ⊒
shiftRightStoreNarrowingEntry (⊒ α ꞉=☆) = ⊒ α ꞉=☆

⇑ʳˢ : StoreNarrowingCtx → StoreNarrowingCtx
⇑ʳˢ = map shiftRightStoreNarrowingEntry

------------------------------------------------------------------------
-- Namespace mediation induced by matched entries
------------------------------------------------------------------------

data StoreMatchedVar : StoreNarrowingCtx → VarCorr where
  smv-here : ∀ {σ α β p B} →
    StoreMatchedVar ((α ꞉ p ꞉ β ⦂ B) ∷ σ) α β

  smv-there : ∀ {σ entry α β} →
    StoreMatchedVar σ α β →
    StoreMatchedVar (entry ∷ σ) α β

------------------------------------------------------------------------
-- Store narrowing
------------------------------------------------------------------------

data StoreNarrowing
    : TyCtx → TyCtx → StoreNarrowingCtx → Set₁ where

  store-nrw-nil : ∀ {ΔL ΔR} →
      -------------------------------
    StoreNarrowing ΔL ΔR []

  store-nrw-both : ∀ {ΔL ΔR σ α β p B} →
    StoreNarrowing ΔL ΔR σ →
    α < ΔL →
    β < ΔR →
    WfTy ΔL (src p) →
    WfTy ΔR B →
    WfTy α (src p) →
    WfTy β B →
    NoStoreEntry α (leftStore σ) →
    NoStoreEntry β (rightStore σ) →
    tag-or-idᵈ ∣ ΔL ∣ leftStore σ ⊢ p ∶ src p ⊒ tgt p →
    MedTy (StoreMatchedVar σ) (tgt p) B →
      ------------------------------------------------
    StoreNarrowing ΔL ΔR ((α ꞉ p ꞉ β ⦂ B) ∷ σ)

  store-nrw-right : ∀ {ΔL ΔR σ β B} →
    StoreNarrowing ΔL ΔR σ →
    β < ΔR →
    WfTy ΔR B →
    WfTy β B →
    NoStoreEntry β (rightStore σ) →
      ---------------------------------------------
    StoreNarrowing ΔL ΔR ((β ꞉= B ⊒) ∷ σ)

  store-nrw-left-star : ∀ {ΔL ΔR σ α} →
    StoreNarrowing ΔL ΔR σ →
    α < ΔL →
    NoStoreEntry α (leftStore σ) →
      -------------------------------------------
    StoreNarrowing ΔL ΔR ((⊒ α ꞉=☆) ∷ σ)

------------------------------------------------------------------------
-- Derived deterministic store well-formedness
------------------------------------------------------------------------

leftStore-det :
  ∀ {ΔL ΔR σ} →
  StoreNarrowing ΔL ΔR σ →
  StoreDetWf ΔL (leftStore σ)
leftStore-det store-nrw-nil =
  record
    { at = record { bound = λ (); wfTy = λ () }
    ; wfOlder = λ ()
    ; unique = λ ()
    }
leftStore-det
    (store-nrw-both σⁿ α< β< hSrc hB hSrc-old hB-old α∉ β∉ p⊒ med) =
  record
    { at =
        record
          { bound = λ
              { (here refl) → α<
              ; (there α∈σ) →
                  StoreWfAt.bound
                    (NWP.StoreDetWf.at (leftStore-det σⁿ)) α∈σ
              }
          ; wfTy = λ
              { (here refl) → hSrc
              ; (there α∈σ) →
                  StoreWfAt.wfTy
                    (NWP.StoreDetWf.at (leftStore-det σⁿ)) α∈σ
              }
          }
    ; wfOlder = λ
        { (here refl) → hSrc-old
        ; (there α∈σ) → NWP.StoreDetWf.wfOlder (leftStore-det σⁿ) α∈σ
        }
    ; unique = λ
        { (here refl) (here refl) → refl
        ; (here refl) (there α∈σ) → ⊥-elim (α∉ α∈σ)
        ; (there α∈σ) (here refl) → ⊥-elim (α∉ α∈σ)
        ; (there α∈σ) (there α∈σ′) →
            NWP.StoreDetWf.unique (leftStore-det σⁿ) α∈σ α∈σ′
        }
    }
leftStore-det (store-nrw-right σⁿ β< hB hB-old β∉) =
  leftStore-det σⁿ
leftStore-det (store-nrw-left-star σⁿ α< α∉) =
  record
    { at =
        record
          { bound = λ
              { (here refl) → α<
              ; (there α∈σ) →
                  StoreWfAt.bound
                    (NWP.StoreDetWf.at (leftStore-det σⁿ)) α∈σ
              }
          ; wfTy = λ
              { (here refl) → wf★
              ; (there α∈σ) →
                  StoreWfAt.wfTy
                    (NWP.StoreDetWf.at (leftStore-det σⁿ)) α∈σ
              }
          }
    ; wfOlder = λ
        { (here refl) → wf★
        ; (there α∈σ) → NWP.StoreDetWf.wfOlder (leftStore-det σⁿ) α∈σ
        }
    ; unique = λ
        { (here refl) (here refl) → refl
        ; (here refl) (there α∈σ) → ⊥-elim (α∉ α∈σ)
        ; (there α∈σ) (here refl) → ⊥-elim (α∉ α∈σ)
        ; (there α∈σ) (there α∈σ′) →
            NWP.StoreDetWf.unique (leftStore-det σⁿ) α∈σ α∈σ′
        }
    }

rightStore-det :
  ∀ {ΔL ΔR σ} →
  StoreNarrowing ΔL ΔR σ →
  StoreDetWf ΔR (rightStore σ)
rightStore-det store-nrw-nil =
  record
    { at = record { bound = λ (); wfTy = λ () }
    ; wfOlder = λ ()
    ; unique = λ ()
    }
rightStore-det
    (store-nrw-both σⁿ α< β< hSrc hB hSrc-old hB-old α∉ β∉ p⊒ med) =
  record
    { at =
        record
          { bound = λ
              { (here refl) → β<
              ; (there β∈σ) →
                  StoreWfAt.bound
                    (NWP.StoreDetWf.at (rightStore-det σⁿ)) β∈σ
              }
          ; wfTy = λ
              { (here refl) → hB
              ; (there β∈σ) →
                  StoreWfAt.wfTy
                    (NWP.StoreDetWf.at (rightStore-det σⁿ)) β∈σ
              }
          }
    ; wfOlder = λ
        { (here refl) → hB-old
        ; (there β∈σ) → NWP.StoreDetWf.wfOlder (rightStore-det σⁿ) β∈σ
        }
    ; unique = λ
        { (here refl) (here refl) → refl
        ; (here refl) (there β∈σ) → ⊥-elim (β∉ β∈σ)
        ; (there β∈σ) (here refl) → ⊥-elim (β∉ β∈σ)
        ; (there β∈σ) (there β∈σ′) →
            NWP.StoreDetWf.unique (rightStore-det σⁿ) β∈σ β∈σ′
        }
    }
rightStore-det (store-nrw-right σⁿ β< hB hB-old β∉) =
  record
    { at =
        record
          { bound = λ
              { (here refl) → β<
              ; (there β∈σ) →
                  StoreWfAt.bound
                    (NWP.StoreDetWf.at (rightStore-det σⁿ)) β∈σ
              }
          ; wfTy = λ
              { (here refl) → hB
              ; (there β∈σ) →
                  StoreWfAt.wfTy
                    (NWP.StoreDetWf.at (rightStore-det σⁿ)) β∈σ
              }
          }
    ; wfOlder = λ
        { (here refl) → hB-old
        ; (there β∈σ) → NWP.StoreDetWf.wfOlder (rightStore-det σⁿ) β∈σ
        }
    ; unique = λ
        { (here refl) (here refl) → refl
        ; (here refl) (there β∈σ) → ⊥-elim (β∉ β∈σ)
        ; (there β∈σ) (here refl) → ⊥-elim (β∉ β∈σ)
        ; (there β∈σ) (there β∈σ′) →
            NWP.StoreDetWf.unique (rightStore-det σⁿ) β∈σ β∈σ′
        }
    }
rightStore-det (store-nrw-left-star σⁿ α< α∉) =
  rightStore-det σⁿ

leftStore-wf :
  ∀ {ΔL ΔR σ} →
  StoreNarrowing ΔL ΔR σ →
  StoreWfAt ΔL (leftStore σ)
leftStore-wf σⁿ = NWP.StoreDetWf.at (leftStore-det σⁿ)

rightStore-wf :
  ∀ {ΔL ΔR σ} →
  StoreNarrowing ΔL ΔR σ →
  StoreWfAt ΔR (rightStore σ)
rightStore-wf σⁿ = NWP.StoreDetWf.at (rightStore-det σⁿ)
