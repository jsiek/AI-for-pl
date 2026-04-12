module Preservation where

-- File Charter:
--   * Type preservation for extrinsic PolyUpDown one-step reduction.
--   * Includes helper lemmas for opening polymorphic casts and ν-down casts.
--   * Uses the extrinsic substitution APIs from `TermProperties.agda`.
-- Note to self:
--   * Keep progress/safety theorems in separate files.
--   * Keep store-shape helper facts in `Store.agda` when they are not
--   * specific to preservation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma as Sigma using (Σ)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; map; []; _∷_)
open import Data.Nat using (zero; suc; z<s; _+_)
open import Data.Product using (Σ; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import TypeProperties
open import Store
open import Ctx using (⤊ᵗ; map-renameˢ-⤊ᵗ)
open import UpDown
open import Terms hiding (_[_]ᵀ)
open import TermProperties
open import Reduction

------------------------------------------------------------------------
-- Opening polymorphic casts at seals
------------------------------------------------------------------------

openCast⊑ :
  ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}{p : Up} →
  ⟰ᵗ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
  (T : Ty) →
  Σ ∣ Φ ⊢ p [ T ]↑ ⦂ A [ T ]ᵗ ⊑ B [ T ]ᵗ
openCast⊑ {Σ = Σ} p T = castWt⊑ (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ) refl ([]⊑ᵗ-wt p T)

openCast⊒ :
  ∀ {Σ : Store}{Φ : List Bool}{A B : Ty}{p : Down} →
  ⟰ᵗ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
  (T : Ty) →
  Σ ∣ Φ ⊢ p [ T ]↓ ⦂ A [ T ]ᵗ ⊒ B [ T ]ᵗ
openCast⊒ {Σ = Σ} p T = castWt⊒ (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ) refl ([]⊒ᵗ-wt p T)

RenOk-false-every :
  ∀ {Ψ} →
  RenOk idˢ (false ∷ every Ψ) (every (suc Ψ))
RenOk-false-every {α = zero} ()
RenOk-false-every {α = suc α} (there p) = there p

renameˢ-pointwise :
  (ρ : Renameˢ) →
  ((α : Seal) → ρ α ≡ α) →
  (A : Ty) →
  renameˢ ρ A ≡ A
renameˢ-pointwise ρ h (＇ X) = refl
renameˢ-pointwise ρ h (｀ α) = cong ｀_ (h α)
renameˢ-pointwise ρ h (‵ ι) = refl
renameˢ-pointwise ρ h ★ = refl
renameˢ-pointwise ρ h (A ⇒ B) = cong₂ _⇒_ (renameˢ-pointwise ρ h A) (renameˢ-pointwise ρ h B)
renameˢ-pointwise ρ h (`∀ A) = cong `∀ (renameˢ-pointwise ρ h A)

mutual
  rename⊑ˢ-pointwise :
    (ρ : Renameˢ) →
    ((α : Seal) → ρ α ≡ α) →
    (p : Up) →
    rename⊑ˢ ρ p ≡ p
  rename⊑ˢ-pointwise ρ h (tag G) = cong tag (renameˢ-pointwise ρ h G)
  rename⊑ˢ-pointwise ρ h (unseal α) = cong unseal (h α)
  rename⊑ˢ-pointwise ρ h (p ↦ q) =
    cong₂ _↦_
      (rename⊒ˢ-pointwise ρ h p)
      (rename⊑ˢ-pointwise ρ h q)
  rename⊑ˢ-pointwise ρ h (∀ᵖ p) =
    cong ∀ᵖ (rename⊑ˢ-pointwise ρ h p)
  rename⊑ˢ-pointwise ρ h (ν p) =
    cong ν_ (rename⊑ˢ-pointwise (extˢ ρ) h-ext p)
    where
      h-ext : (α : Seal) → extˢ ρ α ≡ α
      h-ext zero = refl
      h-ext (suc α) = cong suc (h α)
  rename⊑ˢ-pointwise ρ h (id A) = cong id (renameˢ-pointwise ρ h A)
  rename⊑ˢ-pointwise ρ h (p ； q) =
    cong₂ _；_
      (rename⊑ˢ-pointwise ρ h p)
      (rename⊑ˢ-pointwise ρ h q)

  rename⊒ˢ-pointwise :
    (ρ : Renameˢ) →
    ((α : Seal) → ρ α ≡ α) →
    (p : Down) →
    rename⊒ˢ ρ p ≡ p
  rename⊒ˢ-pointwise ρ h (untag G ℓ) = cong (λ T → untag T ℓ) (renameˢ-pointwise ρ h G)
  rename⊒ˢ-pointwise ρ h (seal α) = cong seal (h α)
  rename⊒ˢ-pointwise ρ h (p ↦ q) =
    cong₂ _↦_
      (rename⊑ˢ-pointwise ρ h p)
      (rename⊒ˢ-pointwise ρ h q)
  rename⊒ˢ-pointwise ρ h (∀ᵖ p) =
    cong ∀ᵖ (rename⊒ˢ-pointwise ρ h p)
  rename⊒ˢ-pointwise ρ h (ν p) =
    cong ν_ (rename⊒ˢ-pointwise (extˢ ρ) h-ext p)
    where
      h-ext : (α : Seal) → extˢ ρ α ≡ α
      h-ext zero = refl
      h-ext (suc α) = cong suc (h α)
  rename⊒ˢ-pointwise ρ h (id A) = cong id (renameˢ-pointwise ρ h A)
  rename⊒ˢ-pointwise ρ h (p ； q) =
    cong₂ _；_
      (rename⊒ˢ-pointwise ρ h p)
      (rename⊒ˢ-pointwise ρ h q)

rename⊑ˢ-id :
  (p : Up) →
  rename⊑ˢ idˢ p ≡ p
rename⊑ˢ-id p = rename⊑ˢ-pointwise idˢ (λ α → refl) p

------------------------------------------------------------------------
-- Dropping a distinguished top-★ lookup when it is permission-forbidden
------------------------------------------------------------------------

removeAtˢ :
  ∀ {Σ : Store}{α : Seal}{A : Ty} →
  Σ ∋ˢ α ⦂ A →
  Store
removeAtˢ {Σ = (beta , ty) ∷ Σ} (Z∋ˢ _ _) = Σ
removeAtˢ {Σ = (beta , ty) ∷ Σ} (S∋ˢ h) = (beta , ty) ∷ removeAtˢ h

data DropLookup
  {Σ : Store}{α : Seal}
  (h★ : Σ ∋ˢ α ⦂ ★)
  {β : Seal}{B : Ty}
  (h : Σ ∋ˢ β ⦂ B) : Set where
  drop-hit :
    β ≡ α →
    B ≡ ★ →
    DropLookup h★ h

  drop-keep :
    removeAtˢ h★ ∋ˢ β ⦂ B →
    DropLookup h★ h

dropLookup :
  ∀ {Σ : Store}{α : Seal}
    (h★ : Σ ∋ˢ α ⦂ ★)
    {β : Seal}{B : Ty}
    (h : Σ ∋ˢ β ⦂ B) →
  DropLookup h★ h
dropLookup (Z∋ˢ α≡δ ★≡D) (Z∋ˢ β≡δ B≡D) = drop-hit (trans β≡δ (sym α≡δ)) (trans B≡D (sym ★≡D))
dropLookup (Z∋ˢ _ _) (S∋ˢ h) = drop-keep h
dropLookup (S∋ˢ h★) (Z∋ˢ β≡δ B≡D) = drop-keep (Z∋ˢ β≡δ B≡D)
dropLookup (S∋ˢ h★) (S∋ˢ h) with dropLookup h★ h
dropLookup (S∋ˢ h★) (S∋ˢ h) | drop-hit β≡α B≡★ = drop-hit β≡α B≡★
dropLookup (S∋ˢ h★) (S∋ˢ h) | drop-keep h′ = drop-keep (S∋ˢ h′)

removeAtˢ-renameLookup-S :
  ∀ {Σ : Store}{α : Seal}{A : Ty}
    (h : Σ ∋ˢ α ⦂ A) →
  removeAtˢ (renameLookupˢ suc h) ≡ ⟰ˢ (removeAtˢ h)
removeAtˢ-renameLookup-S (Z∋ˢ _ _) = refl
removeAtˢ-renameLookup-S {Σ = (beta , ty) ∷ Σ} (S∋ˢ h) = cong₂ _∷_ refl (removeAtˢ-renameLookup-S h)

removeAtˢ-ν-lift :
  ∀ {Σ : Store}{α : Seal}
    (h★ : Σ ∋ˢ α ⦂ ★) →
  removeAtˢ (S∋ˢ (renameLookupˢ suc h★))
    ≡ ((zero , ⇑ˢ ★) ∷ ⟰ˢ (removeAtˢ h★))
removeAtˢ-ν-lift h★ = cong₂ _∷_ refl (removeAtˢ-renameLookup-S h★)

removeAtˢ-renameLookupᵗ :
  ∀ {Σ : Store}{α : Seal}{A : Ty}
    (ρ : Renameᵗ) →
    (h : Σ ∋ˢ α ⦂ A) →
  removeAtˢ (renameLookupᵗ ρ h) ≡ renameStoreᵗ ρ (removeAtˢ h)
removeAtˢ-renameLookupᵗ ρ (Z∋ˢ _ _) = refl
removeAtˢ-renameLookupᵗ {Σ = (beta , ty) ∷ Σ} ρ (S∋ˢ h) = cong₂ _∷_ refl (removeAtˢ-renameLookupᵗ ρ h)

mutual
  drop★⊒-seal-preserving :
    ∀ {Σ : Store}{α : Seal}
      {Φ : List Bool}{A B : Ty}{p : Down} →
    (h★ : Σ ∋ˢ α ⦂ ★) →
    (α ∈ Φ → ⊥) →
    Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    removeAtˢ h★ ∣ Φ ⊢ p ⦂ A ⊒ B
  drop★⊒-seal-preserving h★ α∉Φ (wt-untag g gok ℓ) = wt-untag g gok ℓ
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal h α∈Φ) with dropLookup h★ h
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal h α∈Φ) | drop-hit β≡α B≡★ =
    ⊥-elim (α∉Φ (subst (λ γ → γ ∈ _) β≡α α∈Φ))
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal h α∈Φ) | drop-keep h′ =
    wt-seal h′ α∈Φ
  drop★⊒-seal-preserving h★ α∉Φ (wt-↦ p q) =
    wt-↦
      (drop★⊑-seal-preserving h★ α∉Φ p)
      (drop★⊒-seal-preserving h★ α∉Φ q)
  drop★⊒-seal-preserving h★ α∉Φ (wt-∀ p) =
    wt-∀
      (castWt⊒
        (removeAtˢ-renameLookupᵗ suc h★)
        refl
        (drop★⊒-seal-preserving (renameLookupᵗ suc h★) α∉Φ p))
  drop★⊒-seal-preserving h★ α∉Φ (wt-ν p) =
    wt-ν
      (castWt⊒
        (removeAtˢ-ν-lift h★)
        refl
        (drop★⊒-seal-preserving
          (S∋ˢ (renameLookupˢ suc h★))
          (λ { (there α∈Φ) → α∉Φ α∈Φ })
          p))
  drop★⊒-seal-preserving h★ α∉Φ (wt-id wfA) = wt-id wfA
  drop★⊒-seal-preserving h★ α∉Φ (wt-； p q) =
    wt-；
      (drop★⊒-seal-preserving h★ α∉Φ p)
      (drop★⊒-seal-preserving h★ α∉Φ q)

  drop★⊑-seal-preserving :
    ∀ {Σ : Store}{α : Seal}
      {Φ : List Bool}{A B : Ty}{p : Up} →
    (h★ : Σ ∋ˢ α ⦂ ★) →
    (α ∈ Φ → ⊥) →
    Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    removeAtˢ h★ ∣ Φ ⊢ p ⦂ A ⊑ B
  drop★⊑-seal-preserving h★ α∉Φ (wt-tag g gok) = wt-tag g gok
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal h α∈Φ) with dropLookup h★ h
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal h α∈Φ) | drop-hit β≡α B≡★ =
    ⊥-elim (α∉Φ (subst (λ γ → γ ∈ _) β≡α α∈Φ))
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal h α∈Φ) | drop-keep h′ =
    wt-unseal h′ α∈Φ
  drop★⊑-seal-preserving h★ α∉Φ (wt-↦ p q) =
    wt-↦
      (drop★⊒-seal-preserving h★ α∉Φ p)
      (drop★⊑-seal-preserving h★ α∉Φ q)
  drop★⊑-seal-preserving h★ α∉Φ (wt-∀ p) =
    wt-∀
      (castWt⊑
        (removeAtˢ-renameLookupᵗ suc h★)
        refl
        (drop★⊑-seal-preserving (renameLookupᵗ suc h★) α∉Φ p))
  drop★⊑-seal-preserving h★ α∉Φ (wt-ν p) =
    wt-ν
      (castWt⊑
        (removeAtˢ-ν-lift h★)
        refl
        (drop★⊑-seal-preserving
          (S∋ˢ (renameLookupˢ suc h★))
          (λ { (there α∈Φ) → α∉Φ α∈Φ })
          p))
  drop★⊑-seal-preserving h★ α∉Φ (wt-id wfA) = wt-id wfA
  drop★⊑-seal-preserving h★ α∉Φ (wt-； p q) =
    wt-；
      (drop★⊑-seal-preserving h★ α∉Φ p)
      (drop★⊑-seal-preserving h★ α∉Φ q)

------------------------------------------------------------------------
-- Preservation for raw one-step reduction
------------------------------------------------------------------------

preservation :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{M N : Term}{A : Ty} →
  Uniqueˢ Σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  M —→ N →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ N ⦂ A
preservation uΣ (⊢· (⊢ƛ wfB N⊢) V⊢) (β vV) =
  []-wt N⊢ V⊢
preservation {Σ = Σ} uΣ
  (⊢• {B = B} {T = T}
    (⊢up {A = `∀ A} {B = `∀ B} Φ V⊢ (wt-∀ {A = A} {B = B} {p = p} p⊢))
    wfT)
  β-up-∀ = ⊢up
    Φ
    (cong-⊢⦂ refl refl refl (cong (λ X → X [ T ]ᵗ) eq-src) (⊢• {B = up-src ∅ˢ p} V⊢′ wfT))
    (openCast⊑ p⊢ T)
  where
    eq-src : up-src ∅ˢ p ≡ A
    eq-src = trans (up-src-irrel {Σ = ∅ˢ} {Σ′ = ⟰ᵗ Σ} p) (up-src-align p⊢)

    V⊢′ = cong-⊢⦂ refl refl refl (cong `∀ (sym eq-src)) V⊢
preservation uΣ (⊢· (⊢up Φ V⊢ (wt-↦ p⊢ q⊢)) W⊢) β-up-↦ =
  ⊢up Φ (⊢· V⊢ (⊢down Φ W⊢ p⊢)) q⊢
preservation uΣ (⊢· (⊢down Φ V⊢ (wt-↦ p⊢ q⊢)) W⊢) β-down-↦ =
  ⊢down Φ (⊢· V⊢ (⊢up Φ W⊢ p⊢)) q⊢
preservation uΣ (⊢up Φ V⊢ (wt-id wfA)) id-up = V⊢
preservation uΣ (⊢down Φ V⊢ (wt-id wfA)) id-down = V⊢
preservation uΣ (⊢up Φ₁ (⊢down Φ₂ V⊢ (wt-seal h α∈Φ₂)) (wt-unseal h′ α∈Φ₁))
  seal-unseal = cong-⊢⦂ refl refl refl (lookup-unique uΣ h h′) V⊢
preservation uΣ (⊢down Φ (⊢up Φ′ V⊢ (wt-tag g gok)) (wt-untag g′ gok′ ℓ))
  tag-untag-ok = V⊢
preservation uΣ (⊢down Φ (⊢up Φ′ V⊢ (wt-tag g gok)) (wt-untag h hok ℓ′))
  (tag-untag-bad neq) = ⊢blame ℓ′
preservation uΣ (⊢up Φ V⊢ (wt-； p⊢ q⊢)) β-up-；= ⊢up Φ (⊢up Φ V⊢ p⊢) q⊢
preservation uΣ (⊢down Φ V⊢ (wt-； p⊢ q⊢)) β-down-；= ⊢down Φ (⊢down Φ V⊢ p⊢) q⊢
preservation uΣ (⊢⊕ (⊢$ (κℕ m)) addℕ (⊢$ (κℕ n))) δ-⊕ = ⊢$ (κℕ (m + n))
preservation uΣ (⊢· (⊢blame ℓ) M⊢) blame-·₁ = ⊢blame ℓ
preservation uΣ (⊢· L⊢ (⊢blame ℓ)) (blame-·₂ vV) = ⊢blame ℓ
preservation uΣ (⊢• (⊢blame ℓ) wfT) blame-·α = ⊢blame ℓ
preservation uΣ (⊢up Φ (⊢blame ℓ) p⊢) blame-up = ⊢blame ℓ
preservation uΣ (⊢down Φ (⊢blame ℓ) p⊢) blame-down = ⊢blame ℓ
preservation uΣ (⊢⊕ (⊢blame ℓ) op M⊢) blame-⊕₁ = ⊢blame ℓ
preservation uΣ (⊢⊕ L⊢ op (⊢blame ℓ)) (blame-⊕₂ vL) = ⊢blame ℓ

------------------------------------------------------------------------
-- Preservation for store-threaded one-step reduction
------------------------------------------------------------------------

preservation-step :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Γ : Ctx}{M M′ : Term}{A : Ty}{ρ : Renameˢ} →
  Uniqueˢ Σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Σ ∣ M —→[ ρ ] Σ′ ∣ M′ →
  Sigma.Σ SealCtx
    (λ Ψ′ →
      Sigma.Σ (SealRenameWf Ψ Ψ′ ρ)
        (λ hρ →
          Δ ∣ Ψ′ ∣ Σ′ ∣ map (renameˢ ρ) Γ ⊢ M′ ⦂ renameˢ ρ A))
preservation-step uΣ M⊢ (id-step red) = _ , (λ α<Ψ → α<Ψ) ,
  cong-⊢⦂ refl (sym (map-renameˢ-id _)) refl (sym renameˢ-id) (preservation uΣ M⊢ red)
preservation-step {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} uΣ (⊢• {B = B} {T = T} (⊢Λ V⊢) wfT)
  (β-Λ {V = V}) =
  suc Ψ , SealRenameWf-suc ,
  cong-⊢⦂ refl refl refl (sym (renameˢ-[]ᵗ suc B T))
    (⊢up (every (suc Ψ)) ([]ᵀ-wt V⊢′ (｀ zero) (wfSeal z<s))
      (instCast⊑-wt {A = ⇑ˢ T} {B = ⇑ˢ B} {α = zero} top here))
  where
    top : ((zero , ⇑ˢ T) ∷ ⟰ˢ Σ) ∋ˢ zero ⦂ ⇑ˢ T
    top = Z∋ˢ refl refl

    V⊢↑ : (suc Δ) ∣ (suc Ψ) ∣ ((zero , ⇑ˢ (renameᵗ suc T)) ∷ ⟰ˢ (⟰ᵗ Σ))
        ∣ map (renameˢ suc) (⤊ᵗ Γ) ⊢ ⇑ˢᵐ V ⦂ ⇑ˢ B
    V⊢↑ = wkΣ-term (drop ⊆ˢ-refl) (⇑ˢᵐ-wt V⊢)

    V⊢′ : (suc Δ) ∣ (suc Ψ) ∣ ⟰ᵗ ((zero , ⇑ˢ T) ∷ ⟰ˢ Σ)
        ∣ ⤊ᵗ (map (renameˢ suc) Γ) ⊢ ⇑ˢᵐ V ⦂ ⇑ˢ B
    V⊢′ = cong-⊢⦂ (sym (renameStoreᵗ-cons-⟰ˢ suc T Σ))
        (map-renameˢ-⤊ᵗ suc Γ) refl refl V⊢↑
preservation-step uΣ M⊢ β-down-∀ = {!!}
preservation-step uΣ M⊢ β-down-ν = {!!}
preservation-step uΣ M⊢ β-up-ν = {!!}
preservation-step uΣ (⊢· L⊢ M⊢) (ξ-·₁ red) = {!!}
preservation-step uΣ (⊢· L⊢ M⊢) (ξ-·₂ vV red) = {!!}
preservation-step uΣ (⊢• M⊢ wfT) (ξ-·α red) = {!!}
preservation-step uΣ (⊢up Φ M⊢ hp) (ξ-up red) = {!!}
preservation-step uΣ (⊢down Φ M⊢ hp) (ξ-down red) = {!!}
preservation-step uΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red) = {!!}
preservation-step uΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red) = {!!}

------------------------------------------------------------------------
-- Preservation for store-threaded multi-step reduction
------------------------------------------------------------------------

SealRenameWf-id :
  ∀ {Ψ} →
  SealRenameWf Ψ Ψ idˢ
SealRenameWf-id α<Ψ = α<Ψ

SealRenameWf-comp :
  ∀ {Ψ Ψ′ Ψ″}{ρ : Renameˢ}{ρ′ : Renameˢ} →
  SealRenameWf Ψ Ψ′ ρ →
  SealRenameWf Ψ′ Ψ″ ρ′ →
  SealRenameWf Ψ Ψ″ (λ α → ρ′ (ρ α))
SealRenameWf-comp hρ hρ′ α<Ψ = hρ′ (hρ α<Ψ)

renameˢ-compose :
  (ρ : Renameˢ) (ρ′ : Renameˢ) (A : Ty) →
  renameˢ ρ′ (renameˢ ρ A) ≡ renameˢ (λ α → ρ′ (ρ α)) A
renameˢ-compose ρ ρ′ (＇ X) = refl
renameˢ-compose ρ ρ′ (｀ α) = refl
renameˢ-compose ρ ρ′ (‵ ι) = refl
renameˢ-compose ρ ρ′ ★ = refl
renameˢ-compose ρ ρ′ (A ⇒ B) = cong₂ _⇒_ (renameˢ-compose ρ ρ′ A) (renameˢ-compose ρ ρ′ B)
renameˢ-compose ρ ρ′ (`∀ A) = cong `∀ (renameˢ-compose ρ ρ′ A)

map-renameˢ-compose :
  (ρ : Renameˢ) (ρ′ : Renameˢ) (Γ : Ctx) →
  map (renameˢ ρ′) (map (renameˢ ρ) Γ)
    ≡ map (renameˢ (λ α → ρ′ (ρ α))) Γ
map-renameˢ-compose ρ ρ′ [] = refl
map-renameˢ-compose ρ ρ′ (A ∷ Γ) = cong₂ _∷_ (renameˢ-compose ρ ρ′ A) (map-renameˢ-compose ρ ρ′ Γ)

step-renaming :
  ∀ {Σ Σ′ : Store}{M M′ : Term}{ρ : Renameˢ} →
  Σ ∣ M —→[ ρ ] Σ′ ∣ M′ →
  Renameˢ
step-renaming {ρ = ρ} _ = ρ

multi-preservation :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Γ : Ctx}{M N : Term}{A : Ty} →
  Uniqueˢ Σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Σ ∣ M —↠ Σ′ ∣ N →
  Sigma.Σ SealCtx
    (λ Ψ′ →
      Sigma.Σ Renameˢ
        (λ ρ →
          Sigma.Σ (SealRenameWf Ψ Ψ′ ρ)
            (λ hρ →
              Δ ∣ Ψ′ ∣ Σ′ ∣ map (renameˢ ρ) Γ ⊢ N ⦂ renameˢ ρ A)))
multi-preservation uΣ M⊢ (_ ∎) = _ , idˢ , SealRenameWf-id ,
  cong-⊢⦂ refl (sym (map-renameˢ-id _)) refl (sym renameˢ-id) M⊢
multi-preservation {Γ = Γ} {A = A} uΣ M⊢ (_ —→⟨ L—→M ⟩ M—↠N) = {!!}
