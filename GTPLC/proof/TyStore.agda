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

------------------------------------------------------------------------
-- Pointwise consequences of recursive store well-formedness
------------------------------------------------------------------------

bound : ∀ {Δ Σ α A}
  → StoreWf Δ Σ
  → (α , A) ∈ Σ
  → α < Δ
bound store-empty ()
bound {α = zero} (store-lift wfΣ refl) α,A∈Σ =
  ⊥-elim (∈-⟰ᵗ-zero α,A∈Σ)
bound {α = suc α} (store-lift wfΣ refl) α,A∈Σ
    with ∈-⟰ᵗ-inv α,A∈Σ
bound {α = suc α} (store-lift wfΣ refl) α,A∈Σ
    | A , eq , α,A∈Σ′ =
  s<s (bound wfΣ α,A∈Σ′)
bound (store-bind wfΣ hA refl) (here refl) = z<s
bound (store-bind wfΣ hA refl) (there α,A∈Σ) =
  bound (store-lift wfΣ refl) α,A∈Σ

wfTy : ∀ {Δ Σ α A}
  → StoreWf Δ Σ
  → (α , A) ∈ Σ
  → WfTy Δ A
wfTy store-empty ()
wfTy {α = zero} (store-lift wfΣ refl) α,A∈Σ =
  ⊥-elim (∈-⟰ᵗ-zero α,A∈Σ)
wfTy {α = suc α} (store-lift wfΣ refl) α,A∈Σ
    with ∈-⟰ᵗ-inv α,A∈Σ
wfTy {α = suc α} (store-lift wfΣ refl) α,A∈Σ
    | A , eq , α,A∈Σ′ =
  subst (WfTy _) (sym eq)
    (renameᵗ-preserves-WfTy (wfTy wfΣ α,A∈Σ′) TyRenameWf-suc)
wfTy (store-bind wfΣ hA refl) (here refl) =
  renameᵗ-preserves-WfTy hA TyRenameWf-suc
wfTy (store-bind wfΣ hA refl) (there α,A∈Σ) =
  wfTy (store-lift wfΣ refl) α,A∈Σ

rename-member-inv : ∀ ρ {X A}
  → X ∈ᵗ renameᵗ ρ A
  → ∃[ Y ] (X ≡ ρ Y × Y ∈ᵗ A)
rename-member-inv ρ {A = ＇ Y} var-∈ = Y , refl , var-∈
rename-member-inv ρ {A = A ⇒ B} (∈-fun-left X∈A)
    with rename-member-inv ρ X∈A
rename-member-inv ρ {A = A ⇒ B} (∈-fun-left X∈A)
    | Y , eq , Y∈A =
  Y , eq , ∈-fun-left Y∈A
rename-member-inv ρ {A = A ⇒ B} (∈-fun-right X∈B)
    with rename-member-inv ρ X∈B
rename-member-inv ρ {A = A ⇒ B} (∈-fun-right X∈B)
    | Y , eq , Y∈B =
  Y , eq , ∈-fun-right Y∈B
rename-member-inv ρ {A = `∀ A} (∈-all X∈A)
    with rename-member-inv (extᵗ ρ) X∈A
rename-member-inv ρ {A = `∀ A} (∈-all X∈A)
    | zero , () , Y∈A
rename-member-inv ρ {A = `∀ A} (∈-all X∈A)
    | suc Y , refl , Y∈A =
  Y , refl , ∈-all Y∈A

older : ∀ {Δ Σ X A Y}
  → StoreWf Δ Σ
  → (X , A) ∈ Σ
  → Y ∈ᵗ A
  → X < Y
older store-empty () Y∈A
older {X = zero} (store-lift wfΣ refl) X,A∈Σ Y∈A =
  ⊥-elim (∈-⟰ᵗ-zero X,A∈Σ)
older {X = suc X} (store-lift wfΣ refl) X,A∈Σ Y∈A
    with ∈-⟰ᵗ-inv X,A∈Σ
older {X = suc X} (store-lift wfΣ refl) X,A∈Σ Y∈A
    | A , refl , X,A∈Σ′ with rename-member-inv suc Y∈A
older {X = suc X} (store-lift wfΣ refl) X,A∈Σ Y∈A
    | A , refl , X,A∈Σ′ | Y , refl , Y∈A′ =
  s<s (older wfΣ X,A∈Σ′ Y∈A′)
older (store-bind wfΣ hA refl) (here refl) Y∈A
    with rename-member-inv suc Y∈A
older (store-bind wfΣ hA refl) (here refl) Y∈A
    | Y , refl , Y∈A′ =
  z<s
older (store-bind wfΣ hA refl) (there X,A∈Σ) Y∈A =
  older (store-lift wfΣ refl) X,A∈Σ Y∈A

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

unique : ∀ {Δ Σ α A B}
  → StoreWf Δ Σ
  → (α , A) ∈ Σ
  → (α , B) ∈ Σ
  → A ≡ B
unique store-empty () B∈Σ
unique (store-lift wfΣ refl) A∈Σ B∈Σ =
  StoreUnique-⟰ᵗ (unique wfΣ) A∈Σ B∈Σ
unique (store-bind wfΣ hA refl) A∈Σ B∈Σ =
  StoreUnique-bind (unique wfΣ) A∈Σ B∈Σ

------------------------------------------------------------------------
-- Store well-formedness under type binders and allocation
------------------------------------------------------------------------

StoreWf-⟰ᵗ : ∀ {Δ Σ}
  → StoreWf Δ Σ
  → StoreWf (suc Δ) (⟰ᵗ Σ)
StoreWf-⟰ᵗ wfΣ = store-lift wfΣ refl

StoreWf-bind : ∀ {Δ Σ A}
  → StoreWf Δ Σ
  → WfTy Δ A
  → StoreWf (suc Δ) ((zero , ⇑ᵗ A) ∷ ⟰ᵗ Σ)
StoreWf-bind wfΣ hA = store-bind wfΣ hA refl
