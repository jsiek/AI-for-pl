module Cast where

-- File Charter:
--   * Indexed Cast relation for factorization work.
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
-- Cast: casts equivalent to imprecision
------------------------------------------------------------------------

infix 4 _∣_⊢_⊑ᶜ_ _∣_⊢_⊒ᶜ_
infixl 6 _；⊑ᶜ_ _；⊒ᶜ_

mutual
  data _∣_⊢_⊑ᶜ_ (Σ : Store) (Φ : List CastPerm) : Ty → Ty → Set where
    ⊑ᶜ-tag : ∀ {G}
      → (g : Ground G)
      → ⊢ g ok Φ
      → Σ ∣ Φ ⊢ G ⊑ᶜ ★

    ⊑ᶜ-unseal★ : ∀ {α}
      → Σ ∋ˢ α ⦂ ★
      → α ∈cast Φ
      → Σ ∣ Φ ⊢ ｀ α ⊑ᶜ ★

    ⊑ᶜ-seal : ∀ α
      → Σ ∣ Φ ⊢ ｀ α ⊑ᶜ ｀ α

    ⊑ᶜ-⇒ : ∀ {A A′ B B′}
      → Σ ∣ Φ ⊢ A′ ⊒ᶜ A
      → Σ ∣ Φ ⊢ B ⊑ᶜ B′
      → Σ ∣ Φ ⊢ (A ⇒ B) ⊑ᶜ (A′ ⇒ B′)

    ⊑ᶜ-∀ : ∀ {A B}
      → ⟰ᵗ Σ ∣ Φ ⊢ A ⊑ᶜ B
      → Σ ∣ Φ ⊢ (`∀ A) ⊑ᶜ (`∀ B)

    {-
      Σ, α:=★ ∣ Φ, cs ⊢  A[α]  ⊑  B
      -------------------------------
      Σ ∣ Φ ⊢  ∀X.A[X]  ⊑  B
    -}
    ⊑ᶜ-ν : ∀ {A B}
      → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢  (⇑ˢ A) [ α₀ ]ᵗ  ⊑ᶜ  ⇑ˢ B 
      → Σ ∣ Φ ⊢  `∀ A  ⊑ᶜ  B

    ⊑ᶜ-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ A ⊑ᶜ A

    _；⊑ᶜ_ : ∀ {A B C}
      → Σ ∣ Φ ⊢ A ⊑ᶜ B
      → Σ ∣ Φ ⊢ B ⊑ᶜ C
      → Σ ∣ Φ ⊢ A ⊑ᶜ C

  data _∣_⊢_⊒ᶜ_ (Σ : Store) (Φ : List CastPerm) : Ty → Ty → Set where
    ⊒ᶜ-untag : ∀ {G}
      → (g : Ground G)
      → ⊢ g ok Φ
      → (ℓ : Label)
      → Σ ∣ Φ ⊢ ★ ⊒ᶜ G

    ⊒ᶜ-seal★ : ∀ {α}
      → Σ ∋ˢ α ⦂ ★
      → α ∈cast Φ
      → Σ ∣ Φ ⊢ ★ ⊒ᶜ ｀ α

    ⊒ᶜ-seal : ∀ α
      → Σ ∣ Φ ⊢ ｀ α ⊒ᶜ ｀ α

    ⊒ᶜ-⇒ : ∀ {A A′ B B′}
      → Σ ∣ Φ ⊢ A′ ⊑ᶜ A
      → Σ ∣ Φ ⊢ B ⊒ᶜ B′
      → Σ ∣ Φ ⊢ (A ⇒ B) ⊒ᶜ (A′ ⇒ B′)

    ⊒ᶜ-∀ : ∀ {A B}
      → ⟰ᵗ Σ ∣ Φ ⊢ A ⊒ᶜ B
      → Σ ∣ Φ ⊢ (`∀ A) ⊒ᶜ (`∀ B)

    ⊒ᶜ-ν : ∀ {A B}
      → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ B ⊒ᶜ ((⇑ˢ A) [ α₀ ]ᵗ)
      → Σ ∣ Φ ⊢ B ⊒ᶜ `∀ A

    ⊒ᶜ-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ A ⊒ᶜ A

    _；⊒ᶜ_ : ∀ {A B C}
      → Σ ∣ Φ ⊢ A ⊒ᶜ B
      → Σ ∣ Φ ⊢ B ⊒ᶜ C
      → Σ ∣ Φ ⊢ A ⊒ᶜ C
