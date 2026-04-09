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
open import Data.Nat using (zero; suc; _+_)
open import Data.Product using (Σ; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import TypeProperties
open import Store
open import UpDown
open import Terms hiding (_[_]ᵀ)
open import TermProperties
open import Reduction

------------------------------------------------------------------------
-- Opening polymorphic casts at seals
------------------------------------------------------------------------

openCast⊑ :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}{p : Up} →
  ⟰ᵗ Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B →
  (α : Seal) →
  Σ ∣ Φ ∣ Ξ ⊢ p [ ｀ α ]↑ ⦂ A [ ｀ α ]ᵗ ⊑ B [ ｀ α ]ᵗ
openCast⊑ {Σ = Σ} p α =
  castWt⊑
    (substStoreᵗ-singleTyEnv-⟰ᵗ (｀ α) Σ)
    refl
    refl
    ([]⊑ᵗ-wt p (｀ α))

openCast⊒ :
  ∀ {Σ : Store}{Φ Ξ : List Bool}{A B : Ty}{p : Down} →
  ⟰ᵗ Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B →
  (α : Seal) →
  Σ ∣ Φ ∣ Ξ ⊢ p [ ｀ α ]↓ ⦂ A [ ｀ α ]ᵗ ⊒ B [ ｀ α ]ᵗ
openCast⊒ {Σ = Σ} p α =
  castWt⊒
    (substStoreᵗ-singleTyEnv-⟰ᵗ (｀ α) Σ)
    refl
    refl
    ([]⊒ᵗ-wt p (｀ α))

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
renameˢ-pointwise ρ h (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-pointwise ρ h A) (renameˢ-pointwise ρ h B)
renameˢ-pointwise ρ h (`∀ A) =
  cong `∀ (renameˢ-pointwise ρ h A)

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
  rename⊑ˢ-pointwise ρ h id = refl
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
  rename⊒ˢ-pointwise ρ h id = refl
  rename⊒ˢ-pointwise ρ h (p ； q) =
    cong₂ _；_
      (rename⊒ˢ-pointwise ρ h p)
      (rename⊒ˢ-pointwise ρ h q)

rename⊑ˢ-id :
  (p : Up) →
  rename⊑ˢ idˢ p ≡ p
rename⊑ˢ-id p = rename⊑ˢ-pointwise idˢ (λ α → refl) p

upCast-every :
  ∀ {Ψ}{Σ : Store}
    {Φ Ξ : List Bool}
    {A B : Ty}
    {p : Up} →
  RenOk idˢ Φ (every Ψ) →
  RenOk idˢ Ξ (every Ψ) →
  Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B →
  Σ ∣ every Ψ ∣ every Ψ ⊢ p ⦂ A ⊑ B
upCast-every {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} {p = p} okΦ okΞ hp =
  subst
    (λ q → Σ ∣ every Ψ ∣ every Ψ ⊢ q ⦂ A ⊑ B)
    (rename⊑ˢ-id p)
    (castWt⊑
      (renameStoreˢ-id {Σ = Σ})
      refl
      refl
      (castWt⊑-raw
        renameˢ-id
        renameˢ-id
        (⊑-renameˢ-wt idˢ okΦ okΞ hp)))

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
dropLookup (Z∋ˢ α≡δ ★≡D) (Z∋ˢ β≡δ B≡D) =
  drop-hit (trans β≡δ (sym α≡δ)) (trans B≡D (sym ★≡D))
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
removeAtˢ-renameLookup-S {Σ = (beta , ty) ∷ Σ} (S∋ˢ h) =
  cong₂ _∷_ refl (removeAtˢ-renameLookup-S h)

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
removeAtˢ-renameLookupᵗ {Σ = (beta , ty) ∷ Σ} ρ (S∋ˢ h) =
  cong₂ _∷_ refl (removeAtˢ-renameLookupᵗ ρ h)

mutual
  drop★⊒-seal-preserving :
    ∀ {Σ : Store}{α : Seal}
      {Φ Ξ : List Bool}{A B : Ty}{p : Down} →
    (h★ : Σ ∋ˢ α ⦂ ★) →
    (α ∈ Φ → ⊥) →
    Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B →
    removeAtˢ h★ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B
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
        refl
        (drop★⊒-seal-preserving (renameLookupᵗ suc h★) α∉Φ p))
  drop★⊒-seal-preserving h★ α∉Φ (wt-ν p) =
    wt-ν
      (castWt⊒
        (removeAtˢ-ν-lift h★)
        refl
        refl
        (drop★⊒-seal-preserving
          (S∋ˢ (renameLookupˢ suc h★))
          (λ { (there α∈Φ) → α∉Φ α∈Φ })
          p))
  drop★⊒-seal-preserving h★ α∉Φ wt-id = wt-id
  drop★⊒-seal-preserving h★ α∉Φ (wt-； p q) =
    wt-；
      (drop★⊒-seal-preserving h★ α∉Φ p)
      (drop★⊒-seal-preserving h★ α∉Φ q)

  drop★⊑-seal-preserving :
    ∀ {Σ : Store}{α : Seal}
      {Φ Ξ : List Bool}{A B : Ty}{p : Up} →
    (h★ : Σ ∋ˢ α ⦂ ★) →
    (α ∈ Φ → ⊥) →
    Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B →
    removeAtˢ h★ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B
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
        refl
        (drop★⊑-seal-preserving (renameLookupᵗ suc h★) α∉Φ p))
  drop★⊑-seal-preserving h★ α∉Φ (wt-ν p) =
    wt-ν
      (castWt⊑
        (removeAtˢ-ν-lift h★)
        refl
        refl
        (drop★⊑-seal-preserving
          (S∋ˢ (renameLookupˢ suc h★))
          (λ { (there α∈Φ) → α∉Φ α∈Φ })
          p))
  drop★⊑-seal-preserving h★ α∉Φ wt-id = wt-id
  drop★⊑-seal-preserving h★ α∉Φ (wt-； p q) =
    wt-；
      (drop★⊑-seal-preserving h★ α∉Φ p)
      (drop★⊑-seal-preserving h★ α∉Φ q)

openν-down :
  ∀ {Σ : Store}
    {Φ Ξ : List Bool}
    {A B : Ty}
    {p : Down} →
  ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (false ∷ Φ) ∣ (true ∷ Ξ)
    ⊢ p ⦂ ⇑ˢ B ⊒ ((⇑ˢ A) [ ｀ zero ]ᵗ) →
  (α : Seal) →
  α ∈ Ξ →
  Σ ∣ Φ ∣ Ξ ⊢ p [ α ]↓ˢ ⦂ B ⊒ (A [ ｀ α ]ᵗ)
openν-down {Σ = Σ} {Φ = Φ} {Ξ = Ξ} {A = A} {B = B} p α α∈Ξ =
  castWt⊒
    (renameStoreˢ-single-⟰ˢ α Σ)
    refl
    refl
    (castWt⊒-raw
      src-eq
      tgt-eq
      (⊒-renameˢ-wt
        (singleSealEnv α)
        RenOk-singleSealEnv-false
        (RenOk-singleSealEnv-true α∈Ξ)
        (drop★⊒-seal-preserving top★ top∉Φ p)))
  where
    top★ :
      ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∋ˢ zero ⦂ ★
    top★ = Z∋ˢ refl refl

    top∉Φ :
      zero ∈ (false ∷ Φ) → ⊥
    top∉Φ ()

    src-eq :
      renameˢ (singleSealEnv α) (⇑ˢ B) ≡ B
    src-eq = renameˢ-single-⇑ˢ-id α B

    tgt-eq :
      renameˢ (singleSealEnv α) ((⇑ˢ A) [ ｀ zero ]ᵗ) ≡ (A [ ｀ α ]ᵗ)
    tgt-eq =
      trans
        (renameˢ-[]ᵗ-seal (singleSealEnv α) (⇑ˢ A) zero)
        (cong (λ T → T [ ｀ α ]ᵗ) (renameˢ-single-⇑ˢ-id α A))

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
preservation uΣ (⊢• {α = α} (⊢Λ N⊢) α∈ h) β-Λ =
  []ᵀ-wt N⊢ (｀ α) (wfSeal (every-index α∈))
preservation uΣ (⊢• {α = α} (⊢up V⊢ (wt-∀ p⊢)) α∈ h) β-up-∀ =
  ⊢up
    (⊢• V⊢ α∈ h)
    (openCast⊑ p⊢ α)
preservation uΣ (⊢• {α = α} (⊢down V⊢ (wt-∀ p⊢)) α∈ h) β-down-∀ =
  ⊢down
    (⊢• V⊢ α∈ h)
    (openCast⊒ p⊢ α)
preservation uΣ
  (⊢• {α = α} (⊢down V⊢ (wt-ν {A = Aν} {B = Bν} p⊢)) α∈ h)
  β-down-ν =
  ⊢down
    V⊢
    (openν-down {A = Aν} {B = Bν} p⊢ α α∈)
preservation uΣ (⊢· (⊢up V⊢ (wt-↦ p⊢ q⊢)) W⊢) β-up-↦ =
  ⊢up
    (⊢· V⊢ (⊢down W⊢ p⊢))
    q⊢
preservation uΣ (⊢· (⊢down V⊢ (wt-↦ p⊢ q⊢)) W⊢) β-down-↦ =
  ⊢down
    (⊢· V⊢ (⊢up W⊢ p⊢))
    q⊢
preservation uΣ
  (⊢up {M = V} {A = `∀ Aν} {B = Bν} V⊢ (wt-ν {A = Aν} {B = Bν} p⊢))
  β-up-ν =
  ⊢ν
    wf★
    (⊢up
      (⊢•
        (wkΣ-term (drop ⊆ˢ-refl) (⇑ˢᵐ-wt V⊢))
        here
        (Z∋ˢ refl refl))
      (upCast-every RenOk-id RenOk-false-every p⊢))
preservation uΣ (⊢up V⊢ wt-id) id-up = V⊢
preservation uΣ (⊢down V⊢ wt-id) id-down = V⊢
preservation uΣ
  (⊢up (⊢down V⊢ (wt-seal h α∈)) (wt-unseal h′ α∈′))
  seal-unseal =
  cong-⊢⦂
    refl
    refl
    refl
    (lookup-unique uΣ h h′)
    V⊢
preservation uΣ
  (⊢down (⊢up V⊢ (wt-tag g gok)) (wt-untag g′ gok′ ℓ))
  tag-untag-ok = V⊢
preservation uΣ
  (⊢down (⊢up V⊢ (wt-tag g gok)) (wt-untag h hok ℓ′))
  (tag-untag-bad neq) = ⊢blame ℓ′
preservation uΣ (⊢up V⊢ (wt-； p⊢ q⊢)) β-up-； =
  ⊢up (⊢up V⊢ p⊢) q⊢
preservation uΣ (⊢down V⊢ (wt-； p⊢ q⊢)) β-down-； =
  ⊢down (⊢down V⊢ p⊢) q⊢
preservation uΣ (⊢⊕ (⊢$ (κℕ m)) addℕ (⊢$ (κℕ n))) δ-⊕ =
  ⊢$ (κℕ (m + n))
preservation uΣ (⊢· (⊢blame ℓ) M⊢) blame-·₁ = ⊢blame ℓ
preservation uΣ (⊢· L⊢ (⊢blame ℓ)) (blame-·₂ vV) = ⊢blame ℓ
preservation uΣ (⊢• (⊢blame ℓ) α∈ h) blame-·α = ⊢blame ℓ
preservation uΣ (⊢up (⊢blame ℓ) p⊢) blame-up = ⊢blame ℓ
preservation uΣ (⊢down (⊢blame ℓ) p⊢) blame-down = ⊢blame ℓ
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
preservation-step uΣ M⊢ (id-step red) =
  _ ,
  (λ α<Ψ → α<Ψ) ,
  cong-⊢⦂
    refl
    (sym (map-renameˢ-id _))
    refl
    (sym renameˢ-id)
    (preservation uΣ M⊢ red)
preservation-step uΣ (⊢ν {A = Aν} wfA N⊢) β-ν =
  _ , SealRenameWf-suc , N⊢
preservation-step uΣ (⊢· L⊢ M⊢) (ξ-·₁ red)
  with preservation-step uΣ L⊢ red
... | Ψ′ , hρ , L′⊢ =
  Ψ′ , hρ ,
  ⊢·
    L′⊢
    (wkΣ-term (store-growth red) (renameˢ-wt _ hρ M⊢))
preservation-step uΣ (⊢· L⊢ M⊢) (ξ-·₂ vV red)
  with preservation-step uΣ M⊢ red
... | Ψ′ , hρ , M′⊢ =
  Ψ′ , hρ ,
  ⊢·
    (wkΣ-term (store-growth red) (renameˢ-wt _ hρ L⊢))
    M′⊢
preservation-step uΣ (⊢• {A = A} {α = α} M⊢ α∈ h) (ξ-·α red)
  with preservation-step uΣ M⊢ red
... | Ψ′ , hρ , M′⊢ =
  Ψ′ , hρ ,
  cong-⊢⦂
    refl
    refl
    refl
    (sym (renameˢ-[]ᵗ-seal _ A α))
    (⊢•
      M′⊢
      (RenOk-every hρ α∈)
      (wkLookupˢ (store-growth red) (renameLookupˢ _ h)))
preservation-step uΣ (⊢up {p = p} M⊢ hp) (ξ-up red)
  with preservation-step uΣ M⊢ red
... | Ψ′ , hρ , M′⊢ =
  Ψ′ , hρ ,
  ⊢up
    {p = rename⊑ˢ _ p}
    M′⊢
    (wk⊑
      (store-growth red)
      (⊑-renameˢ-wt _ (RenOk-every hρ) (RenOk-every hρ) hp))
preservation-step uΣ (⊢down {p = p} M⊢ hp) (ξ-down red)
  with preservation-step uΣ M⊢ red
... | Ψ′ , hρ , M′⊢ =
  Ψ′ , hρ ,
  ⊢down
    {p = rename⊒ˢ _ p}
    M′⊢
    (wk⊒
      (store-growth red)
      (⊒-renameˢ-wt _ (RenOk-every hρ) (RenOk-every hρ) hp))
preservation-step uΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₁ red)
  with preservation-step uΣ L⊢ red
... | Ψ′ , hρ , L′⊢ =
  Ψ′ , hρ ,
  ⊢⊕
    L′⊢
    op
    (wkΣ-term (store-growth red) (renameˢ-wt _ hρ M⊢))
preservation-step uΣ (⊢⊕ L⊢ op M⊢) (ξ-⊕₂ vL red)
  with preservation-step uΣ M⊢ red
... | Ψ′ , hρ , M′⊢ =
  Ψ′ , hρ ,
  ⊢⊕
    (wkΣ-term (store-growth red) (renameˢ-wt _ hρ L⊢))
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
renameˢ-compose ρ ρ′ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-compose ρ ρ′ A) (renameˢ-compose ρ ρ′ B)
renameˢ-compose ρ ρ′ (`∀ A) = cong `∀ (renameˢ-compose ρ ρ′ A)

map-renameˢ-compose :
  (ρ : Renameˢ) (ρ′ : Renameˢ) (Γ : Ctx) →
  map (renameˢ ρ′) (map (renameˢ ρ) Γ)
    ≡ map (renameˢ (λ α → ρ′ (ρ α))) Γ
map-renameˢ-compose ρ ρ′ [] = refl
map-renameˢ-compose ρ ρ′ (A ∷ Γ) =
  cong₂ _∷_
    (renameˢ-compose ρ ρ′ A)
    (map-renameˢ-compose ρ ρ′ Γ)

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
multi-preservation uΣ M⊢ (_ ∎) =
  _ , idˢ , SealRenameWf-id ,
  cong-⊢⦂
    refl
    (sym (map-renameˢ-id _))
    refl
    (sym renameˢ-id)
    M⊢
multi-preservation {Γ = Γ} {A = A} uΣ M⊢ (_ —→⟨ L—→M ⟩ M—↠N)
  with preservation-step uΣ M⊢ L—→M
... | Ψ₁ , hρ₁ , M′⊢
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
