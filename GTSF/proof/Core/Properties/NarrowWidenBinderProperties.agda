module proof.Core.Properties.NarrowWidenBinderProperties where

-- File Charter:
--   * Opening and allocation lemmas for narrowing/widening under type binders.
--   * Exports the canonical `∀`-body and `gen`-body transport operations.
--   * Depends only on core narrowing/widening renaming and weakening support.

open import Data.List using (_∷_)
open import Data.Nat using (_<_; suc; zero)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst)

open import Types
open import Store
open import Coercions
open import NarrowWiden
open import proof.Core.Properties.CoercionProperties using
  (single-mode-rename-lower)
open import proof.Core.Properties.TypeProperties using
  ( renameStoreᵗ-single-suc-cancel
  ; singleRenameᵗ-Wf-<
  )


open-narrowing :
  ∀ {μ Δ Σ α c A B} →
  α < Δ →
  extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ A ⊒ B →
  μ ∣ Δ ∣ Σ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ ⊒ B [ α ]ᴿ
open-narrowing {μ = μ} {Σ = Σ} {α = α} α<Δ c⊒ =
  subst
    (λ Σ′ → μ ∣ _ ∣ Σ′ ⊢ _ ∶ _ ⊒ _)
    (renameStoreᵗ-single-suc-cancel α Σ)
    (narrow-renameᵗ
      (singleRenameᵗ-Wf-< α<Δ)
      (single-mode-rename-lower μ α)
      c⊒)

open-widening :
  ∀ {μ Δ Σ α c A B} →
  α < Δ →
  extᵈ μ ∣ suc Δ ∣ ⟰ᵗ Σ ⊢ c ∶ A ⊑ B →
  μ ∣ Δ ∣ Σ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ ⊑ B [ α ]ᴿ
open-widening {μ = μ} {Σ = Σ} {α = α} α<Δ c⊑ =
  subst
    (λ Σ′ → μ ∣ _ ∣ Σ′ ⊢ _ ∶ _ ⊑ _)
    (renameStoreᵗ-single-suc-cancel α Σ)
    (widen-renameᵗ
      (singleRenameᵗ-Wf-< α<Δ)
      (single-mode-rename-lower μ α)
      c⊑)

open-all-narrowing :
  ∀ {μ Δ Σ α c A B} →
  α < Δ →
  μ ∣ Δ ∣ Σ ⊢ `∀ c ∶ `∀ A ⊒ `∀ B →
  μ ∣ Δ ∣ Σ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ ⊒ B [ α ]ᴿ
open-all-narrowing α<Δ (cast-all c⊢ , cross (`∀ cⁿ)) =
  open-narrowing α<Δ (c⊢ , cⁿ)

open-all-widening :
  ∀ {μ Δ Σ α c A B} →
  α < Δ →
  μ ∣ Δ ∣ Σ ⊢ `∀ c ∶ `∀ A ⊑ `∀ B →
  μ ∣ Δ ∣ Σ ⊢ c [ α ]ᶜ ∶ A [ α ]ᴿ ⊑ B [ α ]ᴿ
open-all-widening α<Δ (cast-all c⊢ , cross (`∀ cʷ)) =
  open-widening α<Δ (c⊢ , cʷ)

allocate-all-narrowing :
  ∀ {μ Δ Σ Aν c A B} →
  μ ∣ Δ ∣ Σ ⊢ `∀ c ∶ `∀ A ⊒ `∀ B →
  extᵈ μ ∣ suc Δ ∣ (zero , Aν) ∷ ⟰ᵗ Σ ⊢ c ∶ A ⊒ B
allocate-all-narrowing (cast-all c⊢ , cross (`∀ cⁿ)) =
  narrow-weaken ≤-refl StoreIncl-drop (c⊢ , cⁿ)

allocate-all-widening :
  ∀ {μ Δ Σ Aν c A B} →
  μ ∣ Δ ∣ Σ ⊢ `∀ c ∶ `∀ A ⊑ `∀ B →
  extᵈ μ ∣ suc Δ ∣ (zero , Aν) ∷ ⟰ᵗ Σ ⊢ c ∶ A ⊑ B
allocate-all-widening (cast-all c⊢ , cross (`∀ cʷ)) =
  widen-weaken ≤-refl StoreIncl-drop (c⊢ , cʷ)

allocate-gen-narrowing :
  ∀ {μ Δ Σ Aν c A B} →
  μ ∣ Δ ∣ Σ ⊢ gen A c ∶ A ⊒ `∀ B →
  genᵈ μ ∣ suc Δ ∣ (zero , Aν) ∷ ⟰ᵗ Σ
    ⊢ c ∶ ⇑ᵗ A ⊒ B
allocate-gen-narrowing (cast-gen hA occ c⊢ , gen cᵍ) =
  narrow-weaken ≤-refl StoreIncl-drop
    (c⊢ , genSafe→narrowing cᵍ)
