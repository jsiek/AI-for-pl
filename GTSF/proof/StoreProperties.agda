module proof.StoreProperties where

-- File Charter:
--   * Proof-only metatheory for GTSF stores.
--   * Store well-formedness preservation under weakening/renaming, fresh-store
--     extension, and membership transport through store renaming.
--   * Public store relations and records live in top-level `Store.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (suc; _<_; _≤_)
open import Data.Nat.Properties
  using (n≤1+n; n<1+n; <-≤-trans; <-irrefl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong)

open import Types
open import Store
open import proof.TypeProperties

------------------------------------------------------------------------
-- Store well-formedness
------------------------------------------------------------------------

StoreWfAt-weaken :
  ∀ {Δ Δ′ Σ} →
  Δ ≤ Δ′ →
  StoreWfAt Δ Σ →
  StoreWfAt Δ′ Σ
StoreWfAt-weaken Δ≤Δ′ wfΣ =
  record
    { bound = λ α∈Σ → <-≤-trans (bound wfΣ α∈Σ) Δ≤Δ′
    ; wfTy = λ α∈Σ → WfTy-weakenᵗ (wfTy wfΣ α∈Σ) Δ≤Δ′
    }

StoreWfAt-cons :
  ∀ {Δ Σ α A} →
  α < Δ →
  WfTy Δ A →
  StoreWfAt Δ Σ →
  StoreWfAt Δ ((α , A) ∷ Σ)
StoreWfAt-cons α<Δ hA wfΣ =
  record
    { bound = bound′
    ; wfTy = wfTy′
    }
  where
    bound′ : ∀ {β B} → (β , B) ∈ _ → β < _
    bound′ (here refl) = α<Δ
    bound′ (there β∈Σ) = bound wfΣ β∈Σ

    wfTy′ : ∀ {β B} → (β , B) ∈ _ → WfTy _ B
    wfTy′ (here refl) = hA
    wfTy′ (there β∈Σ) = wfTy wfΣ β∈Σ

StoreWfAt-rename :
  ∀ {Δ Δ′ Σ ρ} →
  TyRenameWf Δ Δ′ ρ →
  StoreWfAt Δ Σ →
  StoreWfAt Δ′ (renameStoreᵗ ρ Σ)
StoreWfAt-rename {Σ = []} hρ wfΣ =
  record { bound = λ (); wfTy = λ () }
StoreWfAt-rename {Σ = (α , A) ∷ Σ} {ρ = ρ} hρ wfΣ =
  record
    { bound = bound′
    ; wfTy = wfTy′
    }
  where
    wfTail : StoreWfAt _ Σ
    wfTail =
      record
        { bound = λ α∈Σ → bound wfΣ (there α∈Σ)
        ; wfTy = λ α∈Σ → wfTy wfΣ (there α∈Σ)
        }

    bound′ : ∀ {β B} → (β , B) ∈ _ → β < _
    bound′ (here refl) = hρ (bound wfΣ (here refl))
    bound′ (there β∈Σ) = bound (StoreWfAt-rename hρ wfTail) β∈Σ

    wfTy′ : ∀ {β B} → (β , B) ∈ _ → WfTy _ B
    wfTy′ (here refl) =
      renameᵗ-preserves-WfTy (wfTy wfΣ (here refl)) hρ
    wfTy′ (there β∈Σ) = wfTy (StoreWfAt-rename hρ wfTail) β∈Σ

StoreWfAt-⟰ᵗ :
  ∀ {Δ Σ} →
  StoreWfAt Δ Σ →
  StoreWfAt (suc Δ) (⟰ᵗ Σ)
StoreWfAt-⟰ᵗ = StoreWfAt-rename TyRenameWf-suc

StoreWf-length∉ :
  ∀ {Δ Σ A} →
  StoreWf Δ Σ →
  (length Σ , A) ∈ Σ →
  ⊥
StoreWf-length∉ wfΣ α∈Σ rewrite len wfΣ =
  <-irrefl refl (bound (at wfΣ) α∈Σ)

StoreWf-fresh-ext :
  ∀ {Δ Σ A} →
  StoreWf Δ Σ →
  WfTy Δ A →
  StoreWf (suc Δ) ((length Σ , A) ∷ Σ)
StoreWf-fresh-ext {Δ = Δ} {Σ = Σ} wfΣ hA =
  record
    { at = StoreWfAt-cons fresh< (WfTy-weakenᵗ hA (n≤1+n Δ))
             (StoreWfAt-weaken (n≤1+n Δ) (at wfΣ))
    ; unique = unique′
    ; len = cong suc (len wfΣ)
    }
  where
    fresh< : length Σ < suc Δ
    fresh< rewrite len wfΣ = n<1+n Δ

    unique′ :
      ∀ {α A B} →
      (α , A) ∈ ((length Σ , _) ∷ Σ) →
      (α , B) ∈ ((length Σ , _) ∷ Σ) →
      A ≡ B
    unique′ (here refl) (here refl) = refl
    unique′ (here refl) (there hB) = ⊥-elim (StoreWf-length∉ wfΣ hB)
    unique′ (there hA) (here refl) = ⊥-elim (StoreWf-length∉ wfΣ hA)
    unique′ (there hA) (there hB) = unique wfΣ hA hB

------------------------------------------------------------------------
-- Store membership transport
------------------------------------------------------------------------

∈-renameStoreᵗ :
  ∀ ρ {Σ α A} →
  (α , A) ∈ Σ →
  (ρ α , renameᵗ ρ A) ∈ renameStoreᵗ ρ Σ
∈-renameStoreᵗ ρ (here refl) = here refl
∈-renameStoreᵗ ρ (there x∈) = there (∈-renameStoreᵗ ρ x∈)

renameStoreᵗ-incl :
  ∀ ρ {Σ Σ′} →
  StoreIncl Σ Σ′ →
  StoreIncl (renameStoreᵗ ρ Σ) (renameStoreᵗ ρ Σ′)
renameStoreᵗ-incl ρ {Σ = []} incl ()
renameStoreᵗ-incl ρ {Σ = (α , A) ∷ Σ} incl (here refl) =
  ∈-renameStoreᵗ ρ (incl (here refl))
renameStoreᵗ-incl ρ {Σ = (α , A) ∷ Σ} incl (there x∈) =
  renameStoreᵗ-incl ρ (λ y∈ → incl (there y∈)) x∈
