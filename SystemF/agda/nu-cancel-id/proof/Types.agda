module nu-cancel-id.proof.Types where

-- File Charter:
--   * RENAMING LEMMAS for `Ty`: congruence, fusion, and the commutation
--     of a shift with a renaming under one binder.  `extⁿ k ρ` is ρ under
--     k binders, the renaming that inserts a cell at depth k when ρ is
--     `suc`.

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import nu-cancel-id.Types

extⁿ : ℕ → Renameᵗ → Renameᵗ
extⁿ zero    ρ = ρ
extⁿ (suc k) ρ = extᵗ (extⁿ k ρ)

ext-cong : ∀ {ρ σ : Renameᵗ}
  → (∀ x → ρ x ≡ σ x)
  → ∀ x → extᵗ ρ x ≡ extᵗ σ x
ext-cong eq zero    = refl
ext-cong eq (suc x) = cong suc (eq x)

rename-cong : ∀ {ρ σ : Renameᵗ}
  → (∀ x → ρ x ≡ σ x)
  → ∀ A → renameᵗ ρ A ≡ renameᵗ σ A
rename-cong eq (` x)   = cong `_ (eq x)
rename-cong eq `ℕ      = refl
rename-cong eq `𝔹      = refl
rename-cong eq (A ⇒ B) = cong₂ _⇒_ (rename-cong eq A) (rename-cong eq B)
rename-cong eq (`∀ A)  = cong `∀ (rename-cong (ext-cong eq) A)

ext-comp : ∀ (ρ σ : Renameᵗ) x
  → extᵗ ρ (extᵗ σ x) ≡ extᵗ (λ y → ρ (σ y)) x
ext-comp ρ σ zero    = refl
ext-comp ρ σ (suc x) = refl

rename-fuse : ∀ (ρ σ : Renameᵗ) A
  → renameᵗ ρ (renameᵗ σ A) ≡ renameᵗ (λ x → ρ (σ x)) A
rename-fuse ρ σ (` x)   = refl
rename-fuse ρ σ `ℕ      = refl
rename-fuse ρ σ `𝔹      = refl
rename-fuse ρ σ (A ⇒ B) = cong₂ _⇒_ (rename-fuse ρ σ A) (rename-fuse ρ σ B)
rename-fuse ρ σ (`∀ A)  =
  cong `∀ (trans (rename-fuse (extᵗ ρ) (extᵗ σ) A)
                 (rename-cong (ext-comp ρ σ) A))

-- a shift commutes with a renaming that goes under one more binder
⇑-ren : ∀ (ρ : Renameᵗ) A → ⇑ᵗ (renameᵗ ρ A) ≡ renameᵗ (extᵗ ρ) (⇑ᵗ A)
⇑-ren ρ A = trans (rename-fuse suc ρ A) (sym (rename-fuse (extᵗ ρ) suc A))
