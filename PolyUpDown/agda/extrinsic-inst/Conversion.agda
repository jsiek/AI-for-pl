module Conversion where

-- File Charter:
--   * Indexed Conversion/Cast for factorization work.
--   * Judgments are indexed by store and permissions, mirroring Up/Down typing.
--   * Rule shapes follow the corresponding `wt-*` Up/Down typing rules.

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Product using (_,_; _×_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; refl; subst; sym; trans)
open import Data.Nat.Properties using (n<1+n; n≤1+n)

open import Types
open import TypeProperties
open import Store
open import UpDown
open import TypeCheckDec using (raiseVarFrom; closeνSrc; open-closeνSrc-id)

------------------------------------------------------------------------
-- Conversion: store-driven seal replacement structure
------------------------------------------------------------------------

infix 4 _∣_⊢_↑ˢ_ _∣_⊢_↓ˢ_
infixl 6 _；↑ˢ_ _；↓ˢ_

mutual
  data _∣_⊢_↑ˢ_ (Σ : Store) (Φ : List CastPerm) : Ty → Ty → Set where
    ↑ˢ-unseal : ∀ {α A}
      → Σ ∋ˢ α ⦂ A
      → α ∈conv Φ
      → Σ ∣ Φ ⊢ ｀ α ↑ˢ A

    ↑ˢ-⇒ : ∀ {A A′ B B′}
      → Σ ∣ Φ ⊢ A′ ↓ˢ A
      → Σ ∣ Φ ⊢ B ↑ˢ B′
      → Σ ∣ Φ ⊢ (A ⇒ B) ↑ˢ (A′ ⇒ B′)

    {-
      ⤊ Σ ∣ Φ ⊢  A[X] ↑ˢ B[X]
      -------------------------------------
      ⤊ Σ ∣ Φ ⊢  ∀X.A[X] ↑ˢ ∀X.B[X]
    -}
    ↑ˢ-∀ : ∀ {A B}
      → ⟰ᵗ Σ ∣ Φ ⊢ A ↑ˢ B
      → Σ ∣ Φ ⊢ (`∀ A) ↑ˢ (`∀ B)

    -- idea: disallow conv seals inside A
    ↑ˢ-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ A ↑ˢ A

    _；↑ˢ_ : ∀ {A B C}
      → Σ ∣ Φ ⊢ A ↑ˢ B
      → Σ ∣ Φ ⊢ B ↑ˢ C
      → Σ ∣ Φ ⊢ A ↑ˢ C

  data _∣_⊢_↓ˢ_ (Σ : Store) (Φ : List CastPerm) : Ty → Ty → Set where
    ↓ˢ-seal : ∀ {α A}
      → Σ ∋ˢ α ⦂ A
      → α ∈conv Φ
      → Σ ∣ Φ ⊢ A ↓ˢ ｀ α

    ↓ˢ-⇒ : ∀ {A A′ B B′}
      → Σ ∣ Φ ⊢ A′ ↑ˢ A
      → Σ ∣ Φ ⊢ B ↓ˢ B′
      → Σ ∣ Φ ⊢ (A ⇒ B) ↓ˢ (A′ ⇒ B′)

    ↓ˢ-∀ : ∀ {A B}
      → ⟰ᵗ Σ ∣ Φ ⊢ A ↓ˢ B
      → Σ ∣ Φ ⊢ (`∀ A) ↓ˢ (`∀ B)

    -- idea: disallow conv seals inside A
    ↓ˢ-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ A ↓ˢ A

    _；↓ˢ_ : ∀ {A B C}
      → Σ ∣ Φ ⊢ A ↓ˢ B
      → Σ ∣ Φ ⊢ B ↓ˢ C
      → Σ ∣ Φ ⊢ A ↓ˢ C
