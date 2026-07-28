module proof.TyStore where

-- File Charter:
--   * Proof-only metatheory for GTPLC type stores.
--   * Provides store inclusion, membership transport, renaming coherence,
--     and preservation of store well-formedness under allocation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; suc; zero; z<s; s<s)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import TyStore
open import proof.TypeInTypeSubst

------------------------------------------------------------------------
-- Inclusion and membership transport
------------------------------------------------------------------------

infix 4 _⊆_
_⊆_ : TyStore → TyStore → Set
Σ ⊆ Σ′ = ∀ {x} → x ∈ Σ → x ∈ Σ′

⊆-refl : ∀ {Σ}
  → Σ ⊆ Σ
⊆-refl x∈ = x∈

⊆-drop : ∀ {Σ α A}
  → Σ ⊆ ((α , A) ∷ Σ)
⊆-drop x∈ = there x∈

⊆-cons : ∀ {Σ Σ′ x}
  → Σ ⊆ Σ′
  → (x ∷ Σ) ⊆ (x ∷ Σ′)
⊆-cons incl (here refl) = here refl
⊆-cons incl (there x∈) = there (incl x∈)

∈-renameTyStoreᵗ : ∀ ρ {Σ α A}
  → (α , A) ∈ Σ
  → (ρ α , renameᵗ ρ A) ∈ renameTyStoreᵗ ρ Σ
∈-renameTyStoreᵗ ρ (here refl) = here refl
∈-renameTyStoreᵗ ρ (there α∈Σ) =
  there (∈-renameTyStoreᵗ ρ α∈Σ)

renameTyStoreᵗ-incl : ∀ ρ {Σ Σ′}
  → Σ ⊆ Σ′
  → renameTyStoreᵗ ρ Σ ⊆ renameTyStoreᵗ ρ Σ′
renameTyStoreᵗ-incl ρ {Σ = []} incl ()
renameTyStoreᵗ-incl ρ {Σ = (α , A) ∷ Σ} incl (here refl) =
  ∈-renameTyStoreᵗ ρ (incl (here refl))
renameTyStoreᵗ-incl ρ {Σ = (α , A) ∷ Σ} incl (there x∈) =
  renameTyStoreᵗ-incl ρ (λ y∈ → incl (there y∈)) x∈

renameTyStoreᵗ-ext-suc-comm : ∀ ρ Σ
  → renameTyStoreᵗ (extᵗ ρ) (⟰ᵗ Σ) ≡
    ⟰ᵗ (renameTyStoreᵗ ρ Σ)
renameTyStoreᵗ-ext-suc-comm ρ [] = refl
renameTyStoreᵗ-ext-suc-comm ρ ((α , A) ∷ Σ) =
  cong₂ _∷_
    (cong₂ _,_ refl (renameᵗ-ext-suc-comm ρ A))
    (renameTyStoreᵗ-ext-suc-comm ρ Σ)

------------------------------------------------------------------------
-- Store well-formedness and allocation
------------------------------------------------------------------------

StoreWf-tail : ∀ {Δ α A Σ}
  → StoreWf Δ ((α , A) ∷ Σ)
  → StoreWf Δ Σ
StoreWf-tail wfΣ =
  record
    { bound = λ x∈ → bound wfΣ (there x∈)
    ; wfTy = λ x∈ → wfTy wfΣ (there x∈)
    ; unique = λ x∈ y∈ →
        unique wfΣ (there x∈) (there y∈)
    }

∈-⟰ᵗ-inv : ∀ {Σ α B}
  → (suc α , B) ∈ ⟰ᵗ Σ
  → ∃[ A ] (B ≡ ⇑ᵗ A × (α , A) ∈ Σ)
∈-⟰ᵗ-inv {Σ = (α , A) ∷ Σ} (here refl) =
  A , refl , here refl
∈-⟰ᵗ-inv {Σ = (β , C) ∷ Σ} (there h)
    with ∈-⟰ᵗ-inv h
∈-⟰ᵗ-inv {Σ = (β , C) ∷ Σ} (there h)
    | A , eq , h′ =
  A , eq , there h′

∈-⟰ᵗ-zero : ∀ {Σ A}
  → (zero , A) ∈ ⟰ᵗ Σ
  → ⊥
∈-⟰ᵗ-zero {Σ = (α , B) ∷ Σ} (there h) =
  ∈-⟰ᵗ-zero h

StoreUnique-⟰ᵗ : ∀ {Σ}
  → (∀ {α A B} → (α , A) ∈ Σ → (α , B) ∈ Σ → A ≡ B)
  → ∀ {α A B}
  → (α , A) ∈ ⟰ᵗ Σ
  → (α , B) ∈ ⟰ᵗ Σ
  → A ≡ B
StoreUnique-⟰ᵗ uniqueΣ {α = zero} h₁ h₂ =
  ⊥-elim (∈-⟰ᵗ-zero h₁)
StoreUnique-⟰ᵗ uniqueΣ {α = suc α} h₁ h₂
    with ∈-⟰ᵗ-inv h₁ | ∈-⟰ᵗ-inv h₂
StoreUnique-⟰ᵗ uniqueΣ {α = suc α} h₁ h₂
    | A , eq₁ , h₁′ | B , eq₂ , h₂′ =
  trans eq₁ (trans (cong ⇑ᵗ (uniqueΣ h₁′ h₂′)) (sym eq₂))

StoreUnique-bind : ∀ {Σ Aν}
  → (∀ {α A B} → (α , A) ∈ Σ → (α , B) ∈ Σ → A ≡ B)
  → ∀ {α A B}
  → (α , A) ∈ ((zero , Aν) ∷ ⟰ᵗ Σ)
  → (α , B) ∈ ((zero , Aν) ∷ ⟰ᵗ Σ)
  → A ≡ B
StoreUnique-bind uniqueΣ (here refl) (here refl) = refl
StoreUnique-bind uniqueΣ (here refl) (there h) =
  ⊥-elim (∈-⟰ᵗ-zero h)
StoreUnique-bind uniqueΣ (there h) (here refl) =
  ⊥-elim (∈-⟰ᵗ-zero h)
StoreUnique-bind uniqueΣ (there h₁) (there h₂) =
  StoreUnique-⟰ᵗ uniqueΣ h₁ h₂

StoreWf-⟰ᵗ : ∀ {Δ Σ}
  → StoreWf Δ Σ
  → StoreWf (suc Δ) (⟰ᵗ Σ)
StoreWf-⟰ᵗ {Δ = Δ} {Σ = Σ} wfΣ =
  record
    { bound = shifted-bound
    ; wfTy = shifted-wfTy
    ; unique = StoreUnique-⟰ᵗ (unique wfΣ)
    }
  where
    shifted-bound : ∀ {α B}
      → (α , B) ∈ ⟰ᵗ Σ
      → α < suc Δ
    shifted-bound {α = zero} h =
      ⊥-elim (∈-⟰ᵗ-zero h)
    shifted-bound {α = suc α} h
        with ∈-⟰ᵗ-inv h
    shifted-bound {α = suc α} h | A , eq , A∈Σ =
      s<s (bound wfΣ A∈Σ)

    shifted-wfTy : ∀ {α B}
      → (α , B) ∈ ⟰ᵗ Σ
      → WfTy (suc Δ) B
    shifted-wfTy {α = zero} h =
      ⊥-elim (∈-⟰ᵗ-zero h)
    shifted-wfTy {α = suc α} h
        with ∈-⟰ᵗ-inv h
    shifted-wfTy {α = suc α} h | A , eq , A∈Σ =
      subst (WfTy (suc Δ)) (sym eq)
        (renameᵗ-preserves-WfTy
          (wfTy wfΣ A∈Σ) TyRenameWf-suc)

StoreWf-bind : ∀ {Δ Σ A}
  → StoreWf Δ Σ
  → WfTy Δ A
  → StoreWf (suc Δ) ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ)
StoreWf-bind {Δ = Δ} {Σ = Σ} {A = A} wfΣ hA =
  record
    { bound = bound′
    ; wfTy = wfTy′
    ; unique = StoreUnique-bind (unique wfΣ)
    }
  where
    shifted-wfΣ : StoreWf (suc Δ) (⟰ᵗ Σ)
    shifted-wfΣ = StoreWf-⟰ᵗ wfΣ

    bound′ : ∀ {α B}
      → (α , B) ∈ ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ)
      → α < suc Δ
    bound′ (here refl) = z<s
    bound′ (there h) = bound shifted-wfΣ h

    wfTy′ : ∀ {α B}
      → (α , B) ∈ ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ)
      → WfTy (suc Δ) B
    wfTy′ (here refl) =
      renameᵗ-preserves-WfTy hA TyRenameWf-suc
    wfTy′ (there h) = wfTy shifted-wfΣ h
