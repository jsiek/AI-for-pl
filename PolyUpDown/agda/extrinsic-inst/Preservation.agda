module Preservation where

-- File Charter:
--   * Type preservation for extrinsic-inst PolyUpDown raw one-step reduction.
--   * Includes helper lemmas for opening polymorphic casts and ν-down casts.
--   * Uses the extrinsic substitution APIs from `TermProperties.agda`.
-- Note to self:
--   * Keep store-threaded preservation in `PreservationFresh.agda`.
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
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Up} →
  suc Δ ∣ Ψ ∣ (⟰ᵗ Σ) ∣ Φ ⊢ p ⦂ A ⊑ B →
  (T : Ty) →
  WfTy Δ Ψ T →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ (p [ T ]↑) ⦂ (A [ T ]ᵗ) ⊑ (B [ T ]ᵗ)
openCast⊑ {Σ = Σ} p T wfT =
  castWt⊑ (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ) refl ([]⊑ᵗ-wt p T wfT)

openCast⊒ :
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p : Down} →
  suc Δ ∣ Ψ ∣ (⟰ᵗ Σ) ∣ Φ ⊢ p ⦂ A ⊒ B →
  (T : Ty) →
  WfTy Δ Ψ T →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ (p [ T ]↓) ⦂ (A [ T ]ᵗ) ⊒ (B [ T ]ᵗ)
openCast⊒ {Σ = Σ} p T wfT =
  castWt⊒ (substStoreᵗ-singleTyEnv-⟰ᵗ T Σ) refl ([]⊒ᵗ-wt p T wfT)

castWt⊒-term :
  ∀ {Δ Ψ}{Σ : Store}{Φ : List CastPerm}{A B : Ty}{p q : Down} →
  p ≡ q →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
  Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ q ⦂ A ⊒ B
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
  rename⊑ˢ-pointwise ρ h (tag p G) =
    cong₂ tag (rename⊑ˢ-pointwise ρ h p) (renameˢ-pointwise ρ h G)
  rename⊑ˢ-pointwise ρ h (unseal α p) =
    cong₂ unseal (h α) (rename⊑ˢ-pointwise ρ h p)
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

  rename⊒ˢ-pointwise :
    (ρ : Renameˢ) →
    ((α : Seal) → ρ α ≡ α) →
    (p : Down) →
    rename⊒ˢ ρ p ≡ p
  rename⊒ˢ-pointwise ρ h (untag G ℓ p) =
    cong₂ (λ T q → untag T ℓ q)
      (renameˢ-pointwise ρ h G)
      (rename⊒ˢ-pointwise ρ h p)
  rename⊒ˢ-pointwise ρ h (seal p α) =
    cong₂ seal (rename⊒ˢ-pointwise ρ h p) (h α)
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
  rename⊑ˢ-right-inverse ρ ρ⁻¹ h (tag p G) =
    cong₂ tag
      (rename⊑ˢ-right-inverse ρ ρ⁻¹ h p)
      (trans
        (renameˢ-compose-local ρ ρ⁻¹ G)
        (renameˢ-pointwise (λ α → ρ⁻¹ (ρ α)) h G))
  rename⊑ˢ-right-inverse ρ ρ⁻¹ h (unseal α p) =
    cong₂ unseal (h α) (rename⊑ˢ-right-inverse ρ ρ⁻¹ h p)
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

  rename⊒ˢ-right-inverse :
    (ρ : Renameˢ) (ρ⁻¹ : Renameˢ) →
    ((α : Seal) → ρ⁻¹ (ρ α) ≡ α) →
    (p : Down) →
    rename⊒ˢ ρ⁻¹ (rename⊒ˢ ρ p) ≡ p
  rename⊒ˢ-right-inverse ρ ρ⁻¹ h (untag G ℓ p) =
    cong₂ (λ T q → untag T ℓ q)
      (trans
        (renameˢ-compose-local ρ ρ⁻¹ G)
        (renameˢ-pointwise (λ α → ρ⁻¹ (ρ α)) h G))
      (rename⊒ˢ-right-inverse ρ ρ⁻¹ h p)
  rename⊒ˢ-right-inverse ρ ρ⁻¹ h (seal p α) =
    cong₂ seal (rename⊒ˢ-right-inverse ρ ρ⁻¹ h p) (h α)
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
    ∀ {Δ Ψ}{Σ : Store}{α : Seal}
      {Φ : List CastPerm}{A B : Ty}{p : Down} →
    (h★ : Σ ∋ˢ α ⦂ ★) →
    (α ∈ Φ → ⊥) →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊒ B →
    Δ ∣ Ψ ∣ (removeAtˢ h★) ∣ Φ ⊢ p ⦂ A ⊒ B
  drop★⊒-seal-preserving h★ α∉Φ (wt-untag g gok ℓ p) =
    wt-untag g gok ℓ (drop★⊒-seal-preserving h★ α∉Φ p)
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal p h α∈Φ) with dropLookup h★ h
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal p h α∈Φ) | drop-hit β≡α B≡★ =
    ⊥-elim (α∉Φ (subst (λ γ → γ ∈ _) β≡α (∈conv⇒∈ α∈Φ)))
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal p h α∈Φ) | drop-keep h′ =
    wt-seal (drop★⊒-seal-preserving h★ α∉Φ p) h′ α∈Φ
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal★ p h α∈Φ) with dropLookup h★ h
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal★ p h α∈Φ) | drop-hit β≡α B≡★ =
    ⊥-elim (α∉Φ (subst (λ γ → γ ∈ _) β≡α (∈cast⇒∈ α∈Φ)))
  drop★⊒-seal-preserving {α = α} h★ α∉Φ (wt-seal★ p h α∈Φ) | drop-keep h′ =
    wt-seal★ (drop★⊒-seal-preserving h★ α∉Φ p) h′ α∈Φ
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

  drop★⊑-seal-preserving :
    ∀ {Δ Ψ}{Σ : Store}{α : Seal}
      {Φ : List CastPerm}{A B : Ty}{p : Up} →
    (h★ : Σ ∋ˢ α ⦂ ★) →
    (α ∈ Φ → ⊥) →
    Δ ∣ Ψ ∣ Σ ∣ Φ ⊢ p ⦂ A ⊑ B →
    Δ ∣ Ψ ∣ (removeAtˢ h★) ∣ Φ ⊢ p ⦂ A ⊑ B
  drop★⊑-seal-preserving h★ α∉Φ (wt-tag p g gok) =
    wt-tag (drop★⊑-seal-preserving h★ α∉Φ p) g gok
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal h α∈Φ p) with dropLookup h★ h
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal h α∈Φ p) | drop-hit β≡α B≡★ =
    ⊥-elim (α∉Φ (subst (λ γ → γ ∈ _) β≡α (∈conv⇒∈ α∈Φ)))
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal h α∈Φ p) | drop-keep h′ =
    wt-unseal h′ α∈Φ (drop★⊑-seal-preserving h★ α∉Φ p)
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal★ h α∈Φ p) with dropLookup h★ h
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal★ h α∈Φ p) | drop-hit β≡α B≡★ =
    ⊥-elim (α∉Φ (subst (λ γ → γ ∈ _) β≡α (∈cast⇒∈ α∈Φ)))
  drop★⊑-seal-preserving {α = α} h★ α∉Φ (wt-unseal★ h α∈Φ p) | drop-keep h′ =
    wt-unseal★ h′ α∈Φ (drop★⊑-seal-preserving h★ α∉Φ p)
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

------------------------------------------------------------------------
-- Preservation for raw one-step reduction
------------------------------------------------------------------------

preservation :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{M N : Term}{A : Ty} →
  StoreWf Δ Ψ Σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  M —→ N →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ N ⦂ A
preservation wfΣ (⊢· (⊢ƛ wfB N⊢) V⊢) (β vV) =
  []-wt N⊢ V⊢
preservation {Σ = Σ} wfΣ
  (⊢• {B = B} {T = T}
    (⊢up {A = `∀ A} {B = `∀ B} Φ lenΦ V⊢ (wt-∀ {A = A} {B = B} {p = p} p⊢))
    wfB wfT)
  (β-up-∀ vV) = ⊢up
    Φ
    lenΦ
    (cong-⊢⦂ refl refl refl (cong (λ X → X [ T ]ᵗ) eq-src)
      (⊢• {B = up-src ∅ˢ p} V⊢′
        (subst
          (WfTy (suc _) _)
          (sym eq-src)
          (⊑-src-wf (storeWf-⟰ᵗ wfΣ) lenΦ p⊢))
        wfT))
    (openCast⊑ p⊢ T wfT)
  where
    eq-src : up-src ∅ˢ p ≡ A
    eq-src = trans (up-src-irrel {Σ = ∅ˢ} {Σ′ = ⟰ᵗ Σ} p) (up-src-align p⊢)

    V⊢′ = cong-⊢⦂ refl refl refl (cong `∀ (sym eq-src)) V⊢
preservation wfΣ (⊢· (⊢up Φ lenΦ V⊢ (wt-↦ p⊢ q⊢)) W⊢) (β-up-↦ vV vW) =
  ⊢up Φ lenΦ (⊢· V⊢ (⊢down Φ lenΦ W⊢ p⊢)) q⊢
preservation wfΣ (⊢· (⊢down Φ lenΦ V⊢ (wt-↦ p⊢ q⊢)) W⊢) (β-down-↦ vV vW) =
  ⊢down Φ lenΦ (⊢· V⊢ (⊢up Φ lenΦ W⊢ p⊢)) q⊢
preservation wfΣ (⊢up Φ lenΦ V⊢ (wt-id wfA)) (id-up vV) = V⊢
preservation wfΣ (⊢down Φ lenΦ V⊢ (wt-id wfA)) (id-down vV) = V⊢
preservation wfΣ
  (⊢up Φ₁ lenΦ₁ (⊢down Φ₂ lenΦ₂ V⊢ (wt-seal p⊢ h α∈Φ₂)) (wt-unseal h′ α∈Φ₁ q⊢))
  (seal-unseal vV) rewrite lookup-unique (storeWf-unique wfΣ) h h′ =
  ⊢up Φ₁ lenΦ₁ (⊢down Φ₂ lenΦ₂ V⊢ p⊢) q⊢
preservation wfΣ
  (⊢up Φ₁ lenΦ₁ (⊢down Φ₂ lenΦ₂ V⊢ (wt-seal p⊢ h α∈Φ₂)) (wt-unseal★ h′ α∈Φ₁ q⊢))
  (seal-unseal vV) rewrite lookup-unique (storeWf-unique wfΣ) h h′ =
  ⊢up Φ₁ lenΦ₁ (⊢down Φ₂ lenΦ₂ V⊢ p⊢) q⊢
preservation wfΣ
  (⊢up Φ₁ lenΦ₁ (⊢down Φ₂ lenΦ₂ V⊢ (wt-seal★ p⊢ h α∈Φ₂)) (wt-unseal h′ α∈Φ₁ q⊢))
  (seal-unseal vV) rewrite lookup-unique (storeWf-unique wfΣ) h h′ =
  ⊢up Φ₁ lenΦ₁ (⊢down Φ₂ lenΦ₂ V⊢ p⊢) q⊢
preservation wfΣ
  (⊢up Φ₁ lenΦ₁ (⊢down Φ₂ lenΦ₂ V⊢ (wt-seal★ p⊢ h α∈Φ₂)) (wt-unseal★ h′ α∈Φ₁ q⊢))
  (seal-unseal vV) rewrite lookup-unique (storeWf-unique wfΣ) h h′ =
  ⊢up Φ₁ lenΦ₁ (⊢down Φ₂ lenΦ₂ V⊢ p⊢) q⊢
preservation wfΣ
  (⊢down Φ lenΦ (⊢up Φ′ lenΦ′ V⊢ (wt-tag p⊢ g gok)) (wt-untag g′ gok′ ℓ q⊢))
  (tag-untag-ok vV) = ⊢down Φ lenΦ (⊢up Φ′ lenΦ′ V⊢ p⊢) q⊢
preservation wfΣ
  (⊢down Φ lenΦ (⊢up Φ′ lenΦ′ V⊢ (wt-tag p⊢ g gok)) (wt-untag h hok ℓ′ q⊢))
  (tag-untag-bad vV neq) = ⊢blame ℓ′
preservation wfΣ (⊢⊕ (⊢$ (κℕ m)) addℕ (⊢$ (κℕ n))) δ-⊕ = ⊢$ (κℕ (m + n))
preservation wfΣ (⊢· (⊢blame ℓ) M⊢) blame-·₁ = ⊢blame ℓ
preservation wfΣ (⊢· L⊢ (⊢blame ℓ)) (blame-·₂ vV) = ⊢blame ℓ
preservation wfΣ (⊢• (⊢blame ℓ) wfB wfT) blame-·α = ⊢blame ℓ
preservation wfΣ (⊢up Φ lenΦ (⊢blame ℓ) p⊢) blame-up = ⊢blame ℓ
preservation wfΣ (⊢down Φ lenΦ (⊢blame ℓ) p⊢) blame-down = ⊢blame ℓ
preservation wfΣ (⊢⊕ (⊢blame ℓ) op M⊢) blame-⊕₁ = ⊢blame ℓ
preservation wfΣ (⊢⊕ L⊢ op (⊢blame ℓ)) (blame-⊕₂ vL) = ⊢blame ℓ
