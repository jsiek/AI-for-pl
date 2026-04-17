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
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; map; []; _∷_)
open import Data.Nat using (zero; suc; z<s; _+_)
open import Data.Product using (Σ; _×_; proj₁; proj₂; _,_)
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
  ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Up} →
  ⟰ᵗ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
  (T : Ty) →
  Σ ∣ Φ ⊢ p [ T ]↑ ⦂ A [ T ]ᵗ ⊑ B [ T ]ᵗ
openCast⊑ {Σ = Σ} p T = castWt⊑ (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ) refl ([]⊑ᵗ-wt p T)

openCast⊒ :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down} →
  ⟰ᵗ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
  (T : Ty) →
  Σ ∣ Φ ⊢ p [ T ]↓ ⦂ A [ T ]ᵗ ⊒ B [ T ]ᵗ
openCast⊒ {Σ = Σ} p T = castWt⊒ (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ) refl ([]⊒ᵗ-wt p T)

castWt⊒-term :
  ∀ {Σ : Store}{Φ : List CastPerm}{A B : Ty}{p q : Down} →
  p ≡ q →
  Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
  Σ ∣ Φ ⊢ q ⦂ A ⊒ B
castWt⊒-term refl h = h

RenOk-false-every :
  ∀ {Ψ} →
  RenOk idˢ (cast-tag ∷ every Ψ) (every (suc Ψ))
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

renameˢ-compose-local :
  (ρ : Renameˢ) (ρ′ : Renameˢ) (A : Ty) →
  renameˢ ρ′ (renameˢ ρ A) ≡ renameˢ (λ α → ρ′ (ρ α)) A
renameˢ-compose-local ρ ρ′ (＇ X) = refl
renameˢ-compose-local ρ ρ′ (｀ α) = refl
renameˢ-compose-local ρ ρ′ (‵ ι) = refl
renameˢ-compose-local ρ ρ′ ★ = refl
renameˢ-compose-local ρ ρ′ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-compose-local ρ ρ′ A) (renameˢ-compose-local ρ ρ′ B)
renameˢ-compose-local ρ ρ′ (`∀ A) =
  cong `∀ (renameˢ-compose-local ρ ρ′ A)

mutual
  rename⊑ˢ-right-inverse :
    (ρ : Renameˢ) (ρ⁻¹ : Renameˢ) →
    ((α : Seal) → ρ⁻¹ (ρ α) ≡ α) →
    (p : Up) →
    rename⊑ˢ ρ⁻¹ (rename⊑ˢ ρ p) ≡ p
  rename⊑ˢ-right-inverse ρ ρ⁻¹ h (tag G) =
    cong tag
      (trans
        (renameˢ-compose-local ρ ρ⁻¹ G)
        (renameˢ-pointwise (λ α → ρ⁻¹ (ρ α)) h G))
  rename⊑ˢ-right-inverse ρ ρ⁻¹ h (unseal α) = cong unseal (h α)
  rename⊑ˢ-right-inverse ρ ρ⁻¹ h (p ↦ q) =
    cong₂ _↦_
      (rename⊒ˢ-right-inverse ρ ρ⁻¹ h p)
      (rename⊑ˢ-right-inverse ρ ρ⁻¹ h q)
  rename⊑ˢ-right-inverse ρ ρ⁻¹ h (∀ᵖ p) =
    cong ∀ᵖ (rename⊑ˢ-right-inverse ρ ρ⁻¹ h p)
  rename⊑ˢ-right-inverse ρ ρ⁻¹ h (ν p) =
    cong ν_ (rename⊑ˢ-right-inverse (extˢ ρ) (extˢ ρ⁻¹) h-ext p)
    where
      h-ext : (α : Seal) → extˢ ρ⁻¹ (extˢ ρ α) ≡ α
      h-ext zero = refl
      h-ext (suc α) = cong suc (h α)
  rename⊑ˢ-right-inverse ρ ρ⁻¹ h (id A) =
    cong id
      (trans
        (renameˢ-compose-local ρ ρ⁻¹ A)
        (renameˢ-pointwise (λ α → ρ⁻¹ (ρ α)) h A))
  rename⊑ˢ-right-inverse ρ ρ⁻¹ h (p ； q) =
    cong₂ _；_
      (rename⊑ˢ-right-inverse ρ ρ⁻¹ h p)
      (rename⊑ˢ-right-inverse ρ ρ⁻¹ h q)

  rename⊒ˢ-right-inverse :
    (ρ : Renameˢ) (ρ⁻¹ : Renameˢ) →
    ((α : Seal) → ρ⁻¹ (ρ α) ≡ α) →
    (p : Down) →
    rename⊒ˢ ρ⁻¹ (rename⊒ˢ ρ p) ≡ p
  rename⊒ˢ-right-inverse ρ ρ⁻¹ h (untag G ℓ) =
    cong (λ T → untag T ℓ)
      (trans
        (renameˢ-compose-local ρ ρ⁻¹ G)
        (renameˢ-pointwise (λ α → ρ⁻¹ (ρ α)) h G))
  rename⊒ˢ-right-inverse ρ ρ⁻¹ h (seal α) = cong seal (h α)
  rename⊒ˢ-right-inverse ρ ρ⁻¹ h (p ↦ q) =
    cong₂ _↦_
      (rename⊑ˢ-right-inverse ρ ρ⁻¹ h p)
      (rename⊒ˢ-right-inverse ρ ρ⁻¹ h q)
  rename⊒ˢ-right-inverse ρ ρ⁻¹ h (∀ᵖ p) =
    cong ∀ᵖ (rename⊒ˢ-right-inverse ρ ρ⁻¹ h p)
  rename⊒ˢ-right-inverse ρ ρ⁻¹ h (ν p) =
    cong ν_ (rename⊒ˢ-right-inverse (extˢ ρ) (extˢ ρ⁻¹) h-ext p)
    where
      h-ext : (α : Seal) → extˢ ρ⁻¹ (extˢ ρ α) ≡ α
      h-ext zero = refl
      h-ext (suc α) = cong suc (h α)
  rename⊒ˢ-right-inverse ρ ρ⁻¹ h (id A) =
    cong id
      (trans
        (renameˢ-compose-local ρ ρ⁻¹ A)
        (renameˢ-pointwise (λ α → ρ⁻¹ (ρ α)) h A))
  rename⊒ˢ-right-inverse ρ ρ⁻¹ h (p ； q) =
    cong₂ _；_
      (rename⊒ˢ-right-inverse ρ ρ⁻¹ h p)
      (rename⊒ˢ-right-inverse ρ ρ⁻¹ h q)

open-shift-⊒-id :
  (p : Down) →
  ((rename⊒ˢ suc p) [ zero ]⊒) ≡ p
open-shift-⊒-id p =
  rename⊒ˢ-right-inverse suc (singleSealEnv zero) (λ α → refl) p

------------------------------------------------------------------------
-- Dropping a distinguished top-★ lookup when it is permission-forbidden
------------------------------------------------------------------------

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

mutual
  drop★⊒-seal-preserving :
    ∀ {Σ : Store}{α : Seal}
      {Φ : List CastPerm}{A B : Ty}{p : Down} →
    (h★ : Σ ∋ˢ α ⦂ ★) →
    (α ∈ Φ → ⊥) →
    Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    removeAtˢ h★ ∣ Φ ⊢ p ⦂ A ⊒ B
  drop★⊒-seal-preserving h★ α∉Φ (wt-untag g gok ℓ) = wt-untag g gok ℓ
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal h α∈Φ) with dropLookup h★ h
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal h α∈Φ) | drop-hit β≡α B≡★ =
    ⊥-elim (α∉Φ (subst (λ γ → γ ∈ _) β≡α (∈conv⇒∈ α∈Φ)))
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal h α∈Φ) | drop-keep h′ =
    wt-seal h′ α∈Φ
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal★ h α∈Φ) with dropLookup h★ h
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal★ h α∈Φ) | drop-hit β≡α B≡★ =
    ⊥-elim (α∉Φ (subst (λ γ → γ ∈ _) β≡α (∈cast⇒∈ α∈Φ)))
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal★ h α∈Φ) | drop-keep h′ =
    wt-seal★ h′ α∈Φ
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
      {Φ : List CastPerm}{A B : Ty}{p : Up} →
    (h★ : Σ ∋ˢ α ⦂ ★) →
    (α ∈ Φ → ⊥) →
    Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    removeAtˢ h★ ∣ Φ ⊢ p ⦂ A ⊑ B
  drop★⊑-seal-preserving h★ α∉Φ (wt-tag g gok) = wt-tag g gok
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal h α∈Φ) with dropLookup h★ h
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal h α∈Φ) | drop-hit β≡α B≡★ =
    ⊥-elim (α∉Φ (subst (λ γ → γ ∈ _) β≡α (∈conv⇒∈ α∈Φ)))
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal h α∈Φ) | drop-keep h′ =
    wt-unseal h′ α∈Φ
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal★ h α∈Φ) with dropLookup h★ h
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal★ h α∈Φ) | drop-hit β≡α B≡★ =
    ⊥-elim (α∉Φ (subst (λ γ → γ ∈ _) β≡α (∈cast⇒∈ α∈Φ)))
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal★ h α∈Φ) | drop-keep h′ =
    wt-unseal★ h′ α∈Φ
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
    (⊢up {A = `∀ A} {B = `∀ B} Φ lenΦ V⊢ (wt-∀ {A = A} {B = B} {p = p} p⊢))
    wfT)
  (β-up-∀ vV) = ⊢up
    Φ
    lenΦ
    (cong-⊢⦂ refl refl refl (cong (λ X → X [ T ]ᵗ) eq-src) (⊢• {B = up-src ∅ˢ p} V⊢′ wfT))
    (openCast⊑ p⊢ T)
  where
    eq-src : up-src ∅ˢ p ≡ A
    eq-src = trans (up-src-irrel {Σ = ∅ˢ} {Σ′ = ⟰ᵗ Σ} p) (up-src-align p⊢)

    V⊢′ = cong-⊢⦂ refl refl refl (cong `∀ (sym eq-src)) V⊢
preservation uΣ (⊢· (⊢up Φ lenΦ V⊢ (wt-↦ p⊢ q⊢)) W⊢) (β-up-↦ vV vW) =
  ⊢up Φ lenΦ (⊢· V⊢ (⊢down Φ lenΦ W⊢ p⊢)) q⊢
preservation uΣ (⊢· (⊢down Φ lenΦ V⊢ (wt-↦ p⊢ q⊢)) W⊢) (β-down-↦ vV vW) =
  ⊢down Φ lenΦ (⊢· V⊢ (⊢up Φ lenΦ W⊢ p⊢)) q⊢
preservation uΣ (⊢up Φ lenΦ V⊢ (wt-id wfA)) (id-up vV) = V⊢
preservation uΣ (⊢down Φ lenΦ V⊢ (wt-id wfA)) (id-down vV) = V⊢
preservation uΣ (⊢up Φ₁ lenΦ₁ (⊢down Φ₂ lenΦ₂ V⊢ (wt-seal h α∈Φ₂)) (wt-unseal h′ α∈Φ₁))
  (seal-unseal vV) = cong-⊢⦂ refl refl refl (lookup-unique uΣ h h′) V⊢
preservation uΣ (⊢up Φ₁ lenΦ₁ (⊢down Φ₂ lenΦ₂ V⊢ (wt-seal h α∈Φ₂)) (wt-unseal★ h′ α∈Φ₁))
  (seal-unseal vV) = cong-⊢⦂ refl refl refl (lookup-unique uΣ h h′) V⊢
preservation uΣ (⊢up Φ₁ lenΦ₁ (⊢down Φ₂ lenΦ₂ V⊢ (wt-seal★ h α∈Φ₂)) (wt-unseal h′ α∈Φ₁))
  (seal-unseal vV) = cong-⊢⦂ refl refl refl (lookup-unique uΣ h h′) V⊢
preservation uΣ (⊢up Φ₁ lenΦ₁ (⊢down Φ₂ lenΦ₂ V⊢ (wt-seal★ h α∈Φ₂)) (wt-unseal★ h′ α∈Φ₁))
  (seal-unseal vV) = cong-⊢⦂ refl refl refl (lookup-unique uΣ h h′) V⊢
preservation uΣ (⊢down Φ lenΦ (⊢up Φ′ lenΦ′ V⊢ (wt-tag g gok)) (wt-untag g′ gok′ ℓ))
  (tag-untag-ok vV) = V⊢
preservation uΣ (⊢down Φ lenΦ (⊢up Φ′ lenΦ′ V⊢ (wt-tag g gok)) (wt-untag h hok ℓ′))
  (tag-untag-bad vV neq) = ⊢blame ℓ′
preservation uΣ (⊢up Φ lenΦ V⊢ (wt-； p⊢ q⊢)) (β-up-； vV) = ⊢up Φ lenΦ (⊢up Φ lenΦ V⊢ p⊢) q⊢
preservation uΣ (⊢down Φ lenΦ V⊢ (wt-； p⊢ q⊢)) (β-down-； vV) = ⊢down Φ lenΦ (⊢down Φ lenΦ V⊢ p⊢) q⊢
preservation uΣ (⊢⊕ (⊢$ (κℕ m)) addℕ (⊢$ (κℕ n))) δ-⊕ = ⊢$ (κℕ (m + n))
preservation uΣ (⊢· (⊢blame ℓ) M⊢) blame-·₁ = ⊢blame ℓ
preservation uΣ (⊢· L⊢ (⊢blame ℓ)) (blame-·₂ vV) = ⊢blame ℓ
preservation uΣ (⊢• (⊢blame ℓ) wfT) blame-·α = ⊢blame ℓ
preservation uΣ (⊢up Φ lenΦ (⊢blame ℓ) p⊢) blame-up = ⊢blame ℓ
preservation uΣ (⊢down Φ lenΦ (⊢blame ℓ) p⊢) blame-down = ⊢blame ℓ
preservation uΣ (⊢⊕ (⊢blame ℓ) op M⊢) blame-⊕₁ = ⊢blame ℓ
preservation uΣ (⊢⊕ L⊢ op (⊢blame ℓ)) (blame-⊕₂ vL) = ⊢blame ℓ

------------------------------------------------------------------------
-- Preservation for store-threaded one-step reduction
------------------------------------------------------------------------

data StepRenShape : Renameˢ → Set where
  shape-id : StepRenShape idˢ
  shape-suc : StepRenShape suc

StepCtxExact : ∀ {ρ} → StepRenShape ρ → SealCtx → SealCtx → Set
StepCtxExact shape-id Ψ Ψ′ = Ψ′ ≡ Ψ
StepCtxExact shape-suc Ψ Ψ′ = Ψ′ ≡ suc Ψ

step-ren-shape :
  ∀ {Σ Σ′ : Store}{M M′ : Term}{ρ : Renameˢ} →
  Σ ∣ M —→[ ρ ] Σ′ ∣ M′ →
  StepRenShape ρ
step-ren-shape (id-step red) = shape-id
step-ren-shape β-Λ = shape-suc
step-ren-shape (β-down-∀ vV) = shape-suc
step-ren-shape (β-down-ν vV) = shape-suc
step-ren-shape (β-up-ν vV) = shape-suc
step-ren-shape (ξ-·₁ red) = step-ren-shape red
step-ren-shape (ξ-·₂ vV red) = step-ren-shape red
step-ren-shape (ξ-·α red) = step-ren-shape red
step-ren-shape (ξ-up red) = step-ren-shape red
step-ren-shape (ξ-down red) = step-ren-shape red
step-ren-shape (ξ-⊕₁ red) = step-ren-shape red
step-ren-shape (ξ-⊕₂ vL red) = step-ren-shape red

preservation-step :
  ∀ {Δ Ψ}{Σ Σ′ : Store}{Γ : Ctx}{M M′ : Term}{A : Ty}{ρ : Renameˢ} →
  Uniqueˢ Σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  (red : Σ ∣ M —→[ ρ ] Σ′ ∣ M′) →
  Sigma.Σ SealCtx
    (λ Ψ′ →
      Sigma.Σ (SealRenameWf Ψ Ψ′ ρ)
        (λ hρ →
          StepCtxExact (step-ren-shape red) Ψ Ψ′ ×
          Δ ∣ Ψ′ ∣ Σ′ ∣ map (renameˢ ρ) Γ ⊢ M′ ⦂ renameˢ ρ A))

preservation-step {Ψ = Ψ} uΣ M⊢ (id-step red) =
  Ψ , (λ α<Ψ → α<Ψ) , refl ,
  cong-⊢⦂ refl (sym (map-renameˢ-id _)) refl (sym renameˢ-id) (preservation uΣ M⊢ red)
preservation-step {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} uΣ (⊢• {B = B} {T = T} (⊢Λ V⊢) wfT)
  (β-Λ {V = V}) =
  suc Ψ , SealRenameWf-suc , refl ,
  cong-⊢⦂ refl refl refl (sym (renameˢ-[]ᵗ suc B T))
    (⊢up (every (suc Ψ)) (length-every (suc Ψ)) ([]ᵀ-wt V⊢′ (α₀) (wfSeal z<s))
      (instCast⊑-wt {A = ⇑ˢ T} {B = ⇑ˢ B} {α = zero} top here-conv-only))
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
preservation-step {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ} uΣ
  (⊢• {B = B} {T = T}
    (⊢down {A = `∀ C} {B = `∀ B} Φ lenΦ V⊢ (wt-∀ {A = C} {B = B} {p = p} p⊢))
    wfT)
  (β-down-∀ {A = T} {B = B} {V = V} {p = p} vV) =
  suc Ψ , SealRenameWf-suc , refl ,
  cong-⊢⦂ refl refl refl out-eq
    (⊢up
      (every (suc Ψ))
      (length-every (suc Ψ))
      (⊢down
        (cast-tag ∷ Φ)
        (mapΦ-suc-length-ren {Φ = Φ} lenΦ)
        (⊢• {B = ⇑ˢ (down-src (⟰ᵗ Σ) p)} V⊢′ (wfSeal z<s))
        (openCast⊒ p⊢′ (α₀)))
      (instCast⊑-wt {A = ⇑ˢ T} {B = ⇑ˢ (down-tgt (⟰ᵗ Σ) p)} {α = zero} top here-conv-only))
  where
    top : ((zero , ⇑ˢ T) ∷ ⟰ˢ Σ) ∋ˢ zero ⦂ ⇑ˢ T
    top = Z∋ˢ refl refl

    eq-src : down-src (⟰ᵗ Σ) p ≡ C
    eq-src = down-src-align (unique-⟰ᵗ uΣ) p⊢

    eq-tgt : down-tgt (⟰ᵗ Σ) p ≡ B
    eq-tgt = down-tgt-align p⊢

    V⊢↑ : Δ ∣ (suc Ψ) ∣ ((zero , ⇑ˢ T) ∷ ⟰ˢ Σ)
        ∣ map (renameˢ suc) Γ ⊢ ⇑ˢᵐ V ⦂ `∀ (⇑ˢ C)
    V⊢↑ = wkΣ-term (drop ⊆ˢ-refl) (⇑ˢᵐ-wt V⊢)

    V⊢′ : Δ ∣ (suc Ψ) ∣ ((zero , ⇑ˢ T) ∷ ⟰ˢ Σ)
        ∣ map (renameˢ suc) Γ ⊢ ⇑ˢᵐ V ⦂ `∀ (⇑ˢ (down-src (⟰ᵗ Σ) p))
    V⊢′ = cong-⊢⦂ refl refl refl (cong `∀ (cong ⇑ˢ (sym eq-src))) V⊢↑

    p⊢↑ : ((zero , ⇑ˢ (renameᵗ suc T)) ∷ ⟰ˢ (⟰ᵗ Σ)) ∣ (cast-tag ∷ Φ)
        ⊢ rename⊒ˢ suc p ⦂ ⇑ˢ C ⊒ ⇑ˢ B
    p⊢↑ =
      wk⊒
        (drop ⊆ˢ-refl)
        (⊒-renameˢ-wt suc RenOkConv-suc RenOkCast-suc RenOkTag-suc p⊢)

    p⊢″ : ⟰ᵗ ((zero , ⇑ˢ T) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ)
        ⊢ rename⊒ˢ suc p ⦂ ⇑ˢ C ⊒ ⇑ˢ B
    p⊢″ = castWt⊒ (sym (renameStoreᵗ-cons-⟰ˢ suc T Σ)) refl p⊢↑

    p⊢′ : ⟰ᵗ ((zero , ⇑ˢ T) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ)
        ⊢ rename⊒ˢ suc p ⦂ ⇑ˢ (down-src (⟰ᵗ Σ) p) ⊒ ⇑ˢ (down-tgt (⟰ᵗ Σ) p)
    p⊢′ = castWt⊒-raw (cong ⇑ˢ (sym eq-src)) (cong ⇑ˢ (sym eq-tgt)) p⊢″

    out-eq :
      (⇑ˢ (down-tgt (⟰ᵗ Σ) p) [ ⇑ˢ T ]ᵗ) ≡ renameˢ suc (B [ T ]ᵗ)
    out-eq = trans
      (cong (λ X → X [ ⇑ˢ T ]ᵗ) (cong ⇑ˢ eq-tgt))
      (sym (renameˢ-[]ᵗ suc B T))
preservation-step
  {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ}
  uΣ
  (⊢• {B = Aν} {T = T}
    (⊢down {A = Bν} {B = `∀ Aν} Φ lenΦ V⊢ (wt-ν {A = Aν} {B = Bν} {p = p} p⊢))
    wfT)
  (β-down-ν {A = T} {B = Aν} {V = V} {p = p} vV) =
  suc Ψ , SealRenameWf-suc , refl ,
  cong-⊢⦂ refl refl refl (sym (renameˢ-[]ᵗ suc Aν T))
    (⊢up
      (every (suc Ψ))
      (length-every (suc Ψ))
      (⊢down
        (cast-tag ∷ Φ)
        (mapΦ-suc-length-ren {Φ = Φ} lenΦ)
        V⊢↑
        p⊢′)
      (instCast⊑-wt {A = ⇑ˢ T} {B = ⇑ˢ Aν} {α = zero} top here-conv-only))
  where
    top : ((zero , ⇑ˢ T) ∷ ⟰ˢ Σ) ∋ˢ zero ⦂ ⇑ˢ T
    top = Z∋ˢ refl refl

    top★ : ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∋ˢ zero ⦂ ★
    top★ = Z∋ˢ refl refl

    top∉Φ : zero ∈ (cast-tag ∷ Φ) → ⊥
    top∉Φ ()

    V⊢↑ : Δ ∣ (suc Ψ) ∣ ((zero , ⇑ˢ T) ∷ ⟰ˢ Σ)
        ∣ map (renameˢ suc) Γ ⊢ ⇑ˢᵐ V ⦂ ⇑ˢ Bν
    V⊢↑ = wkΣ-term (drop ⊆ˢ-refl) (⇑ˢᵐ-wt V⊢)

    p⊢drop : ⟰ˢ Σ ∣ (cast-tag ∷ Φ) ⊢ p ⦂ ⇑ˢ Bν ⊒ ((⇑ˢ Aν) [ α₀ ]ᵗ)
    p⊢drop = drop★⊒-seal-preserving top★ top∉Φ p⊢

    p⊢base : ((zero , ⇑ˢ T) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ p ⦂ ⇑ˢ Bν ⊒ ((⇑ˢ Aν) [ α₀ ]ᵗ)
    p⊢base = wk⊒ (drop ⊆ˢ-refl) p⊢drop

    p⊢′ : ((zero , ⇑ˢ T) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ)
        ⊢ ((rename⊒ˢ suc p) [ zero ]⊒) ⦂ ⇑ˢ Bν ⊒ ((⇑ˢ Aν) [ α₀ ]ᵗ)
    p⊢′ = castWt⊒-term (sym (open-shift-⊒-id p)) p⊢base
preservation-step
  {Δ = Δ} {Ψ = Ψ} {Σ = Σ} {Γ = Γ}
  uΣ
  (⊢up {A = `∀ Aν} {B = Bν} Φ lenΦ V⊢ (wt-ν {A = Aν} {B = Bν} {p = p} p⊢))
  (β-up-ν {V = V} {p = p} vV) =
  suc Ψ , SealRenameWf-suc , refl ,
  ⊢up
    (cast-seal ∷ Φ)
    (mapΦ-suc-length-ren {Φ = Φ} lenΦ)
    (⊢• {B = ⇑ˢ ((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ)}
      V⊢′
      (wfSeal z<s))
    p⊢′
  where
    eq-src : up-src ((zero , ★) ∷ ⟰ˢ Σ) p ≡ (⇑ˢ Aν) [ α₀ ]ᵗ
    eq-src = up-src-align p⊢

    eq-close : ((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ) ≡ Aν
    eq-close =
      trans
        (cong (λ X → (⇑ᵗ X) [ ＇ zero ]ˢᵗ) eq-src)
        (closeν-inline-open Aν)

    eq-open :
      (⇑ˢ ((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ) [ α₀ ]ᵗ)
        ≡ ((⇑ˢ Aν) [ α₀ ]ᵗ)
    eq-open = cong (λ X → (⇑ˢ X) [ α₀ ]ᵗ) eq-close

    V⊢↑ : Δ ∣ (suc Ψ) ∣ ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ)
        ∣ map (renameˢ suc) Γ ⊢ ⇑ˢᵐ V ⦂ `∀ (⇑ˢ Aν)
    V⊢↑ = wkΣ-term (drop ⊆ˢ-refl) (⇑ˢᵐ-wt V⊢)

    V⊢′ : Δ ∣ (suc Ψ) ∣ ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ)
        ∣ map (renameˢ suc) Γ ⊢ ⇑ˢᵐ V ⦂ `∀ (⇑ˢ ((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ))
    V⊢′ = cong-⊢⦂ refl refl refl (cong `∀ (cong ⇑ˢ (sym eq-close))) V⊢↑

    p⊢′ : ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ)
        ⊢ p ⦂ (⇑ˢ ((⇑ᵗ (up-src ((zero , ★) ∷ ⟰ˢ Σ) p)) [ ＇ zero ]ˢᵗ) [ α₀ ]ᵗ) ⊑ ⇑ˢ Bν
    p⊢′ = castWt⊑-raw (sym eq-open) refl p⊢
preservation-step {Ψ = Ψ} uΣ (⊢· L⊢ M⊢) (ξ-·₁ red)
  with step-ren-shape red | preservation-step uΣ L⊢ red
preservation-step {Ψ = Ψ} uΣ (⊢· L⊢ M⊢) (ξ-·₁ red)
  | shape-id | Ψ′ , hρ , eqΨ′ , L′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    ⊢·
      L′⊢
      (wkΣ-term
        (store-growth red)
        (renameˢ-wt
          idˢ
          hρ
          (λ Φ → Φ)
          (λ lenΦ → trans lenΦ (sym eqΨ′))
          RenOk-id RenOkConv-id RenOkCast-id RenOkTag-id RenNotIn-id
          M⊢))
preservation-step {Ψ = Ψ} uΣ (⊢· L⊢ M⊢) (ξ-·₁ red)
  | shape-suc | Ψ′ , hρ , eqΨ′ , L′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    ⊢·
      L′⊢
      (wkΣ-term
        (store-growth red)
        (renameˢ-wt
          suc
          hρ
          mapΦ-suc
          (λ {Φ = Φ₀} lenΦ₀ →
            trans (mapΦ-suc-length-ren {Φ = Φ₀} lenΦ₀) (sym eqΨ′))
          RenOk-suc RenOkConv-suc RenOkCast-suc RenOkTag-suc RenNotIn-suc
          M⊢))
preservation-step {Ψ = Ψ} uΣ (⊢· L⊢ M⊢) (ξ-·₂ vV red)
  with step-ren-shape red | preservation-step uΣ M⊢ red
preservation-step {Ψ = Ψ} uΣ (⊢· L⊢ M⊢) (ξ-·₂ vV red)
  | shape-id | Ψ′ , hρ , eqΨ′ , M′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    ⊢·
      (wkΣ-term
        (store-growth red)
        (renameˢ-wt
          idˢ
          hρ
          (λ Φ → Φ)
          (λ lenΦ → trans lenΦ (sym eqΨ′))
          RenOk-id RenOkConv-id RenOkCast-id RenOkTag-id RenNotIn-id
          L⊢))
      M′⊢
preservation-step {Ψ = Ψ} uΣ (⊢· L⊢ M⊢) (ξ-·₂ vV red)
  | shape-suc | Ψ′ , hρ , eqΨ′ , M′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    ⊢·
      (wkΣ-term
        (store-growth red)
        (renameˢ-wt
          suc
          hρ
          mapΦ-suc
          (λ {Φ = Φ₀} lenΦ₀ →
            trans (mapΦ-suc-length-ren {Φ = Φ₀} lenΦ₀) (sym eqΨ′))
          RenOk-suc RenOkConv-suc RenOkCast-suc RenOkTag-suc RenNotIn-suc
          L⊢))
      M′⊢
preservation-step {Ψ = Ψ} uΣ (⊢• {B = B} {T = T} M⊢ wfT) (ξ-·α red)
  with preservation-step uΣ M⊢ red
preservation-step {Ψ = Ψ} uΣ (⊢• {B = B} {T = T} M⊢ wfT) (ξ-·α red)
  | Ψ′ , hρ , eqΨ′ , M′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    cong-⊢⦂
      refl
      refl
      refl
      (sym (renameˢ-[]ᵗ _ B T))
      (⊢•
        M′⊢
        (renameˢ-preserves-WfTy wfT hρ))
preservation-step {Ψ = Ψ} uΣ (⊢up Φ lenΦ M⊢ hp) (ξ-up red)
  with step-ren-shape red | preservation-step uΣ M⊢ red
preservation-step {Ψ = Ψ} uΣ (⊢up Φ lenΦ M⊢ hp) (ξ-up red)
  | shape-id | Ψ′ , hρ , eqΨ′ , M′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    ⊢up
      Φ
      (trans lenΦ (sym eqΨ′))
      M′⊢
      (wk⊑
        (store-growth red)
        (⊑-renameˢ-wt idˢ RenOkConv-id RenOkCast-id RenOkTag-id hp))
preservation-step {Ψ = Ψ} uΣ (⊢up Φ lenΦ M⊢ hp) (ξ-up red)
  | shape-suc | Ψ′ , hρ , eqΨ′ , M′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    ⊢up
      (mapΦ-suc Φ)
      (trans (mapΦ-suc-length-ren {Φ = Φ} lenΦ) (sym eqΨ′))
      M′⊢
      (wk⊑
        (store-growth red)
        (⊑-renameˢ-wt suc RenOkConv-suc RenOkCast-suc RenOkTag-suc hp))
preservation-step {Ψ = Ψ} uΣ (⊢down Φ lenΦ M⊢ hp) (ξ-down red)
  with step-ren-shape red | preservation-step uΣ M⊢ red
preservation-step {Ψ = Ψ} uΣ (⊢down Φ lenΦ M⊢ hp) (ξ-down red)
  | shape-id | Ψ′ , hρ , eqΨ′ , M′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    ⊢down
      Φ
      (trans lenΦ (sym eqΨ′))
      M′⊢
      (wk⊒
        (store-growth red)
        (⊒-renameˢ-wt idˢ RenOkConv-id RenOkCast-id RenOkTag-id hp))
preservation-step {Ψ = Ψ} uΣ (⊢down Φ lenΦ M⊢ hp) (ξ-down red)
  | shape-suc | Ψ′ , hρ , eqΨ′ , M′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    ⊢down
      (mapΦ-suc Φ)
      (trans (mapΦ-suc-length-ren {Φ = Φ} lenΦ) (sym eqΨ′))
      M′⊢
      (wk⊒
        (store-growth red)
        (⊒-renameˢ-wt suc RenOkConv-suc RenOkCast-suc RenOkTag-suc hp))
preservation-step {Ψ = Ψ} uΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red)
  with step-ren-shape red | preservation-step uΣ L⊢ red
preservation-step {Ψ = Ψ} uΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red)
  | shape-id | Ψ′ , hρ , eqΨ′ , L′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    ⊢⊕
      L′⊢
      op
      (wkΣ-term
        (store-growth red)
        (renameˢ-wt
          idˢ
          hρ
          (λ Φ → Φ)
          (λ lenΦ → trans lenΦ (sym eqΨ′))
          RenOk-id RenOkConv-id RenOkCast-id RenOkTag-id RenNotIn-id
          M⊢))
preservation-step {Ψ = Ψ} uΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red)
  | shape-suc | Ψ′ , hρ , eqΨ′ , L′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    ⊢⊕
      L′⊢
      op
      (wkΣ-term
        (store-growth red)
        (renameˢ-wt
          suc
          hρ
          mapΦ-suc
          (λ {Φ = Φ₀} lenΦ₀ →
            trans (mapΦ-suc-length-ren {Φ = Φ₀} lenΦ₀) (sym eqΨ′))
          RenOk-suc RenOkConv-suc RenOkCast-suc RenOkTag-suc RenNotIn-suc
          M⊢))
preservation-step {Ψ = Ψ} uΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red)
  with step-ren-shape red | preservation-step uΣ M⊢ red
preservation-step {Ψ = Ψ} uΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red)
  | shape-id | Ψ′ , hρ , eqΨ′ , M′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    ⊢⊕
      (wkΣ-term
        (store-growth red)
        (renameˢ-wt
          idˢ
          hρ
          (λ Φ → Φ)
          (λ lenΦ → trans lenΦ (sym eqΨ′))
          RenOk-id RenOkConv-id RenOkCast-id RenOkTag-id RenNotIn-id
          L⊢))
      op
      M′⊢
preservation-step {Ψ = Ψ} uΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red)
  | shape-suc | Ψ′ , hρ , eqΨ′ , M′⊢ =
    Ψ′ , hρ , eqΨ′ ,
    ⊢⊕
      (wkΣ-term
        (store-growth red)
        (renameˢ-wt
          suc
          hρ
          mapΦ-suc
          (λ {Φ = Φ₀} lenΦ₀ →
            trans (mapΦ-suc-length-ren {Φ = Φ₀} lenΦ₀) (sym eqΨ′))
          RenOk-suc RenOkConv-suc RenOkCast-suc RenOkTag-suc RenNotIn-suc
          L⊢))
      op
      M′⊢

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
multi-preservation {Γ = Γ} {A = A} uΣ M⊢ (_ —→⟨ L—→M ⟩ M—↠N)
  with preservation-step uΣ M⊢ L—→M
... | Ψ₁ , hρ₁ , eqρ₁ , M′⊢
  with multi-preservation (unique-store-step uΣ L—→M) M′⊢ M—↠N
... | Ψ₂ , ρ₂ , hρ₂ , N⊢ =
  Ψ₂ ,
  (λ α → ρ₂ ((step-renaming L—→M) α)) ,
  SealRenameWf-comp hρ₁ hρ₂ ,
  cong-⊢⦂
    refl
    (map-renameˢ-compose (step-renaming L—→M) ρ₂ Γ)
    refl
    (renameˢ-compose (step-renaming L—→M) ρ₂ A)
    N⊢
