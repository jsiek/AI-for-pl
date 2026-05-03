module Cast where

-- File Charter:
--   * Indexed Cast relation for factorization work.
--   * Judgments are indexed by store and permissions, mirroring Up/Down typing.
--   * Rule shapes follow the corresponding `wt-*` Up/Down typing rules.

open import Data.Empty using (⊥)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Product using (_,_; _×_; ∃; ∃-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; refl; subst; sym; trans)
open import Data.Nat.Properties using (n<1+n; n≤1+n)

open import Types
open import TypeProperties
open import Store
open import UpDown
open import TypeCheckDec using (raiseVarFrom; closeνSrc; open-closeνSrc-id)
open import ImprecisionIndexed using (occurs)

------------------------------------------------------------------------
-- Cast: casts equivalent to imprecision
------------------------------------------------------------------------

infix 4 _∣_⊢_⊑ᶜ_ _∣_⊢_⊒ᶜ_

CleanSeal : List CastPerm → Seal → Set
CleanSeal Φ α = (α ∈cast Φ → ⊥) × (α ∈tag Φ → ⊥)

Clean : List CastPerm → Ty → Set
Clean Φ (＇ X) = ⊤
Clean Φ (｀ α) = CleanSeal Φ α
Clean Φ (‵ ι) = ⊤
Clean Φ ★ = ⊤
Clean Φ (A ⇒ B) = Clean Φ A × Clean Φ B
Clean Φ (`∀ A) = Clean Φ A

Clean-⇑ˢ :
  ∀ {Φ A b} →
  Clean Φ A →
  Clean (b ∷ Φ) (⇑ˢ A)
Clean-⇑ˢ {A = ＇ X} clean = tt
Clean-⇑ˢ {A = ｀ α} (α∉cast , α∉tag) =
  (λ { (there-cast α∈cast) → α∉cast α∈cast }) ,
  (λ { (there-tag α∈tag) → α∉tag α∈tag })
Clean-⇑ˢ {A = ‵ ι} clean = tt
Clean-⇑ˢ {A = ★} clean = tt
Clean-⇑ˢ {A = A ⇒ B} (cleanA , cleanB) =
  Clean-⇑ˢ {A = A} cleanA , Clean-⇑ˢ {A = B} cleanB
Clean-⇑ˢ {A = `∀ A} clean = Clean-⇑ˢ {A = A} clean

Clean-⇑ˢ-inv :
  ∀ {Φ A b} →
  Clean (b ∷ Φ) (⇑ˢ A) →
  Clean Φ A
Clean-⇑ˢ-inv {A = ＇ X} clean = tt
Clean-⇑ˢ-inv {A = ｀ α} (sα∉cast , sα∉tag) =
  (λ α∈cast → sα∉cast (there-cast α∈cast)) ,
  (λ α∈tag → sα∉tag (there-tag α∈tag))
Clean-⇑ˢ-inv {A = ‵ ι} clean = tt
Clean-⇑ˢ-inv {A = ★} clean = tt
Clean-⇑ˢ-inv {A = A ⇒ B} (cleanA , cleanB) =
  Clean-⇑ˢ-inv {A = A} cleanA , Clean-⇑ˢ-inv {A = B} cleanB
Clean-⇑ˢ-inv {A = `∀ A} clean = Clean-⇑ˢ-inv {A = A} clean

mutual
  data _∣_⊢_⊑ᶜ_ (Σ : Store) (Φ : List CastPerm) : Ty → Ty → Set where
    ⊑ᶜ-tag : ∀ {A G}
      → Σ ∣ Φ ⊢ A ⊑ᶜ G
      → (g : Ground G)
      → ⊢ g ok Φ
      → Σ ∣ Φ ⊢ A ⊑ᶜ ★

    ⊑ᶜ-unseal★ : ∀ {α B}
      → Σ ∣ Φ ⊢ B ⊑ᶜ ｀ α
      → Σ ∋ˢ α ⦂ ★
      → α ∈cast Φ
      → Σ ∣ Φ ⊢ B ⊑ᶜ ★

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
      → .(occurs zero A ≡ true)
      → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢  (⇑ˢ A) [ α₀ ]ᵗ  ⊑ᶜ  ⇑ˢ B 
      → Σ ∣ Φ ⊢  `∀ A  ⊑ᶜ  B

    ⊑ᶜ-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ A ⊑ᶜ A

  data _∣_⊢_⊒ᶜ_ (Σ : Store) (Φ : List CastPerm) : Ty → Ty → Set where
    ⊒ᶜ-untag : ∀ {G B}
      → (g : Ground G)
      → ⊢ g ok Φ
      → (ℓ : Label)
      → Σ ∣ Φ ⊢ G ⊒ᶜ B
      → Σ ∣ Φ ⊢ ★ ⊒ᶜ B

    ⊒ᶜ-seal★ : ∀ {A α}
      → Σ ∣ Φ ⊢ ｀ α ⊒ᶜ A
      → Σ ∋ˢ α ⦂ ★
      → α ∈cast Φ
      → Σ ∣ Φ ⊢ ★ ⊒ᶜ A

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
      → .(occurs zero A ≡ true)
      → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ B ⊒ᶜ ((⇑ˢ A) [ α₀ ]ᵗ)
      → Σ ∣ Φ ⊢ B ⊒ᶜ `∀ A

    ⊒ᶜ-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ A ⊒ᶜ A
