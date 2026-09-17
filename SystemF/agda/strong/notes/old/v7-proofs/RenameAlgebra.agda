module strong.proof.RenameAlgebra where

-- Strong System F v7 — the algebra of renamings.
--
-- Every rule that carries a term or a conversion under NEW ANCHORS renames
-- the anchor coordinate: `Beta`'s crossΛ and `Wrap` by `renAnchᴹ`, `Merge`
-- by `renConv`, `TyWrap` by `shiftByᴿ`.  The weakening lemma therefore has
-- to push renamings past each other, and past the `⇑ᴿ` that `∋r` applies
-- when it reads a representation out of a context.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import strong.Types
open import strong.RepresentationTypes
open import strong.CtxMorph using (shiftAnchor)

------------------------------------------------------------------------
-- Source types
------------------------------------------------------------------------

renameᵗ-cong : ∀ {ρ₁ ρ₂ : Renameᵗ} → (∀ X → ρ₁ X ≡ ρ₂ X)
  → ∀ A → renameᵗ ρ₁ A ≡ renameᵗ ρ₂ A
renameᵗ-cong h (` X) = cong `_ (h X)
renameᵗ-cong h `ℕ = refl
renameᵗ-cong h `𝔹 = refl
renameᵗ-cong h (A ⇒ B) = cong₂ _⇒_ (renameᵗ-cong h A) (renameᵗ-cong h B)
renameᵗ-cong {ρ₁} {ρ₂} h (`∀ A) = cong `∀ (renameᵗ-cong h′ A)
  where
  h′ : ∀ X → extᵗ ρ₁ X ≡ extᵗ ρ₂ X
  h′ zero = refl
  h′ (suc X) = cong suc (h X)

renameᵗ-id : ∀ {ρ : Renameᵗ} → (∀ X → ρ X ≡ X) → ∀ A → renameᵗ ρ A ≡ A
renameᵗ-id h (` X) = cong `_ (h X)
renameᵗ-id h `ℕ = refl
renameᵗ-id h `𝔹 = refl
renameᵗ-id h (A ⇒ B) = cong₂ _⇒_ (renameᵗ-id h A) (renameᵗ-id h B)
renameᵗ-id {ρ} h (`∀ A) = cong `∀ (renameᵗ-id h′ A)
  where
  h′ : ∀ X → extᵗ ρ X ≡ X
  h′ zero = refl
  h′ (suc X) = cong suc (h X)

------------------------------------------------------------------------
-- Representation types
------------------------------------------------------------------------

renameᴿ-cong : ∀ {ρ₁ ρ₂ : Renameᴿ} → (∀ α → ρ₁ α ≡ ρ₂ α)
  → ∀ R → renameᴿ ρ₁ R ≡ renameᴿ ρ₂ R
renameᴿ-cong h (`α α) = cong `α (h α)
renameᴿ-cong h `ℕᴿ = refl
renameᴿ-cong h `𝔹ᴿ = refl
renameᴿ-cong h (R ⇒ᴿ S) = cong₂ _⇒ᴿ_ (renameᴿ-cong h R) (renameᴿ-cong h S)
renameᴿ-cong {ρ₁} {ρ₂} h (`∀ᴿ R) = cong `∀ᴿ (renameᴿ-cong h′ R)
  where
  h′ : ∀ α → extᴿ ρ₁ α ≡ extᴿ ρ₂ α
  h′ zero = refl
  h′ (suc α) = cong suc (h α)

renameᴿ-id : ∀ {ρ : Renameᴿ} → (∀ α → ρ α ≡ α) → ∀ R → renameᴿ ρ R ≡ R
renameᴿ-id h (`α α) = cong `α (h α)
renameᴿ-id h `ℕᴿ = refl
renameᴿ-id h `𝔹ᴿ = refl
renameᴿ-id h (R ⇒ᴿ S) = cong₂ _⇒ᴿ_ (renameᴿ-id h R) (renameᴿ-id h S)
renameᴿ-id {ρ} h (`∀ᴿ R) = cong `∀ᴿ (renameᴿ-id h′ R)
  where
  h′ : ∀ α → extᴿ ρ α ≡ α
  h′ zero = refl
  h′ (suc α) = cong suc (h α)

renameᴿ-fuse : ∀ (ρ₁ ρ₂ : Renameᴿ) R
  → renameᴿ ρ₁ (renameᴿ ρ₂ R) ≡ renameᴿ (λ α → ρ₁ (ρ₂ α)) R
renameᴿ-fuse ρ₁ ρ₂ (`α α) = refl
renameᴿ-fuse ρ₁ ρ₂ `ℕᴿ = refl
renameᴿ-fuse ρ₁ ρ₂ `𝔹ᴿ = refl
renameᴿ-fuse ρ₁ ρ₂ (R ⇒ᴿ S) =
  cong₂ _⇒ᴿ_ (renameᴿ-fuse ρ₁ ρ₂ R) (renameᴿ-fuse ρ₁ ρ₂ S)
renameᴿ-fuse ρ₁ ρ₂ (`∀ᴿ R) =
  cong `∀ᴿ (trans (renameᴿ-fuse (extᴿ ρ₁) (extᴿ ρ₂) R)
                  (renameᴿ-cong h R))
  where
  h : ∀ α → extᴿ ρ₁ (extᴿ ρ₂ α) ≡ extᴿ (λ β → ρ₁ (ρ₂ β)) α
  h zero = refl
  h (suc α) = refl

-- The commutation the `∋r` transport turns on: `∋r` hands back a
-- representation already shifted by one, and a weakening must push its own
-- renaming past that shift.
⇑ᴿ-comm : ∀ (ρ : Renameᴿ) R → renameᴿ (extᴿ ρ) (⇑ᴿ R) ≡ ⇑ᴿ (renameᴿ ρ R)
⇑ᴿ-comm ρ R =
  trans (renameᴿ-fuse (extᴿ ρ) suc R)
        (sym (renameᴿ-fuse suc ρ R))

-- `shiftByᴿ` is iterated `⇑ᴿ`; as a renaming it is `shiftAnchor`.
shiftByᴿ-rename : ∀ k R → shiftByᴿ k R ≡ renameᴿ (shiftAnchor k) R
shiftByᴿ-rename zero R = sym (renameᴿ-id (λ α → refl) R)
shiftByᴿ-rename (suc k) R =
  trans (shiftByᴿ-rename k (⇑ᴿ R))
        (trans (renameᴿ-fuse (shiftAnchor k) suc R)
               (renameᴿ-cong (λ α → +-suc k α) R))
