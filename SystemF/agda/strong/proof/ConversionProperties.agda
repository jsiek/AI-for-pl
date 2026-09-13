module strong.proof.ConversionProperties where

-- Strong System F v7 — inversion facts for typed conversions.

open import Data.Nat using (ℕ; zero)
open import Data.List using (_∷_)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import strong.Types
open import strong.Ctx
open import strong.Conversion

mutual
  conv-target : ∀ {Δ₁ Δ₂ c A B}
    → Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂
    → target c ≡ B
  conv-target (conv-id same _) = refl
  conv-target (conv-cons head tail) = tail-target tail

  tail-target : ∀ {Δ₁ Δ₂ c A B}
    → Δ₁ ⊩ c ∶ A ⇝ B ⊣ Δ₂
    → target c ≡ B
  tail-target (tail-id wf) = refl
  tail-target (tail-cons head tail) = tail-target tail

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

same-fun-left : ∀ {Δ₁ Δ₂ A B C}
  → SameTy zero Δ₁ A Δ₂ (B ⇒ C)
  → FunShape A
same-fun-left (same-⇒ a b) = fun-shape _ _

same-ℕ-right : ∀ {Δ₁ Δ₂ B}
  → SameTy zero Δ₁ `ℕ Δ₂ B
  → B ≡ `ℕ
same-ℕ-right same-ℕ = refl

same-𝔹-right : ∀ {Δ₁ Δ₂ B}
  → SameTy zero Δ₁ `𝔹 Δ₂ B
  → B ≡ `𝔹
same-𝔹-right same-𝔹 = refl

------------------------------------------------------------------------
-- The spine of a derivation
------------------------------------------------------------------------

sb-uncons : ∀ {Δ₁ Δ₂ e₁ e₂}
  → SameBindings (e₁ ∷ Δ₁) (e₂ ∷ Δ₂) → SameBindings Δ₁ Δ₂
sb-uncons (sb-∷ s) = s

mutual
  head-sb : ∀ {Δ₁ Δ₂ h A B}
    → Δ₁ ⊢̂ h ∶ A ⇝ B ⊣ Δ₂ → SameBindings Δ₁ Δ₂
  head-sb (conv-seal x r rd flip) = flip-sb flip
  head-sb (conv-unseal x r rd flip) = sb-sym (flip-sb flip)
  head-sb (conv-fun s t) = sb-sym (conv-sb s)
  head-sb (conv-all s) = sb-uncons (conv-sb s)

  conv-sb : ∀ {Δ₁ Δ₂ c A B}
    → Δ₁ ⊢ c ∶ A ⇝ B ⊣ Δ₂ → SameBindings Δ₁ Δ₂
  conv-sb (conv-id same sb) = sb
  conv-sb (conv-cons hd tl) = sb-trans (head-sb hd) (tail-sb tl)

  tail-sb : ∀ {Δ₁ Δ₂ c A B}
    → Δ₁ ⊩ c ∶ A ⇝ B ⊣ Δ₂ → SameBindings Δ₁ Δ₂
  tail-sb (tail-id wf) = sb-refl
  tail-sb (tail-cons hd tl) = sb-trans (head-sb hd) (tail-sb tl)
