module proof.NuStoreProperties where

-- File Charter:
--   * Proof-only metatheory for Nu GTSF stores.
--   * Store well-formedness preservation under weakening/renaming,
--     arbitrary-fresh store extension, and membership transport through store
--     renaming.
--   * The sparse Nu store invariant lives in top-level `NuStore.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; _<_; _≤_; z<s)
open import Data.Nat.Properties using (<-≤-trans)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Types
open import NuStore
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

∈-domˢ :
  ∀ {Σ α A} →
  (α , A) ∈ Σ →
  α ∈ domˢ Σ
∈-domˢ (here refl) = here refl
∈-domˢ (there α∈Σ) = there (∈-domˢ α∈Σ)

StoreWf-fresh-ext :
  ∀ {Δ Δ′ Σ α A} →
  StoreWf Δ Σ →
  Δ ≤ Δ′ →
  Δ ≤ α →
  α < Δ′ →
  WfTy Δ A →
  α ∉ domˢ Σ →
  StoreWf Δ′ ((α , A) ∷ Σ)
StoreWf-fresh-ext wfΣ Δ≤Δ′ Δ≤α α<Δ′ hA α∉Σ =
  record
    { at = StoreWfAt-cons α<Δ′ (WfTy-weakenᵗ hA Δ≤Δ′)
             (StoreWfAt-weaken Δ≤Δ′ (at wfΣ))
    ; unique = unique′
    }
  where
    unique′ :
      ∀ {β B C} →
      (β , B) ∈ ((_ , _) ∷ _) →
      (β , C) ∈ ((_ , _) ∷ _) →
      B ≡ C
    unique′ (here refl) (here refl) = refl
    unique′ (here refl) (there hB) = ⊥-elim (α∉Σ (∈-domˢ hB))
    unique′ (there hA) (here refl) = ⊥-elim (α∉Σ (∈-domˢ hA))
    unique′ (there hA) (there hB) = unique wfΣ hA hB

∈-⟰ᵗ-inv :
  ∀ {Σ α B} →
  (suc α , B) ∈ ⟰ᵗ Σ →
  ∃[ A ] (B ≡ ⇑ᵗ A × (α , A) ∈ Σ)
∈-⟰ᵗ-inv {Σ = (α , A) ∷ Σ} (here refl) =
  A , refl , here refl
∈-⟰ᵗ-inv {Σ = (β , C) ∷ Σ} (there h)
    with ∈-⟰ᵗ-inv h
∈-⟰ᵗ-inv {Σ = (β , C) ∷ Σ} (there h)
    | A , eq , h′ =
  A , eq , there h′

∈-⟰ᵗ-zero :
  ∀ {Σ A} →
  (zero , A) ∈ ⟰ᵗ Σ →
  ⊥
∈-⟰ᵗ-zero {Σ = (α , B) ∷ Σ} (there h) =
  ∈-⟰ᵗ-zero h

StoreUnique-⟰ᵗ :
  ∀ {Σ} →
  (∀ {α A B} → (α , A) ∈ Σ → (α , B) ∈ Σ → A ≡ B) →
  ∀ {α A B} → (α , A) ∈ ⟰ᵗ Σ → (α , B) ∈ ⟰ᵗ Σ → A ≡ B
StoreUnique-⟰ᵗ uniqueΣ {α = zero} h₁ h₂ =
  ⊥-elim (∈-⟰ᵗ-zero h₁)
StoreUnique-⟰ᵗ uniqueΣ {α = suc α} h₁ h₂
    with ∈-⟰ᵗ-inv h₁ | ∈-⟰ᵗ-inv h₂
StoreUnique-⟰ᵗ uniqueΣ {α = suc α} h₁ h₂
    | A , eq₁ , h₁′ | B , eq₂ , h₂′ =
  trans eq₁ (trans (cong ⇑ᵗ (uniqueΣ h₁′ h₂′)) (sym eq₂))

StoreWf-⟰ᵗ :
  ∀ {Δ Σ} →
  StoreWf Δ Σ →
  StoreWf (suc Δ) (⟰ᵗ Σ)
StoreWf-⟰ᵗ wfΣ =
  record
    { at = StoreWfAt-⟰ᵗ (at wfΣ)
    ; unique = StoreUnique-⟰ᵗ (unique wfΣ)
    }

StoreUnique-bind :
  ∀ {Σ Aν} →
  (∀ {α A B} → (α , A) ∈ Σ → (α , B) ∈ Σ → A ≡ B) →
  ∀ {α A B} →
  (α , A) ∈ ((zero , Aν) ∷ ⟰ᵗ Σ) →
  (α , B) ∈ ((zero , Aν) ∷ ⟰ᵗ Σ) →
  A ≡ B
StoreUnique-bind uniqueΣ (here refl) (here refl) = refl
StoreUnique-bind uniqueΣ (here refl) (there h) =
  ⊥-elim (∈-⟰ᵗ-zero h)
StoreUnique-bind uniqueΣ (there h) (here refl) =
  ⊥-elim (∈-⟰ᵗ-zero h)
StoreUnique-bind uniqueΣ (there h₁) (there h₂) =
  StoreUnique-⟰ᵗ uniqueΣ h₁ h₂

StoreWf-bind :
  ∀ {Δ Σ A} →
  StoreWf Δ Σ →
  WfTy Δ A →
  StoreWf (suc Δ) ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ)
StoreWf-bind wfΣ hA =
  record
    { at = StoreWfAt-cons z<s
             (renameᵗ-preserves-WfTy hA TyRenameWf-suc)
             (StoreWfAt-⟰ᵗ (at wfΣ))
    ; unique = StoreUnique-bind (unique wfΣ)
    }

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
