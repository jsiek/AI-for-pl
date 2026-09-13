module strong.proof.ConversionProperties where

-- Strong System F v7 — inversion facts for typed conversions.

open import Data.Nat using (ℕ; zero)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import strong.Types
open import strong.Ctx
open import strong.Conversion

conv-target : ∀ {Δ₁ Δ₂ c A B}
  → Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂
  → target c ≡ B
conv-target (conv-id same) = refl
conv-target (conv-cons head tail) = conv-target tail

data VarShape : Ty → Set where
  var-shape : ∀ X → VarShape (` X)

data FunShape : Ty → Set where
  fun-shape : ∀ A B → FunShape (A ⇒ B)

data AllShape : Ty → Set where
  all-shape : ∀ A → AllShape (`∀ A)

same-var-right : ∀ {Δ₁ Δ₂ X B}
  → SameTy zero Δ₁ (` X) Δ₂ B
  → VarShape B
same-var-right (same-free x y anchor) = var-shape _

same-fun-right : ∀ {Δ₁ Δ₂ A B C}
  → SameTy zero Δ₁ (A ⇒ B) Δ₂ C
  → FunShape C
same-fun-right (same-⇒ a b) = fun-shape _ _

same-all-right : ∀ {Δ₁ Δ₂ A B}
  → SameTy zero Δ₁ (`∀ A) Δ₂ B
  → AllShape B
same-all-right (same-∀ a) = all-shape _

same-all-left : ∀ {Δ₁ Δ₂ A B}
  → SameTy zero Δ₁ A Δ₂ (`∀ B)
  → AllShape A
same-all-left (same-∀ a) = all-shape _

same-ℕ-right : ∀ {Δ₁ Δ₂ B}
  → SameTy zero Δ₁ `ℕ Δ₂ B
  → B ≡ `ℕ
same-ℕ-right same-ℕ = refl

same-𝔹-right : ∀ {Δ₁ Δ₂ B}
  → SameTy zero Δ₁ `𝔹 Δ₂ B
  → B ≡ `𝔹
same-𝔹-right same-𝔹 = refl
