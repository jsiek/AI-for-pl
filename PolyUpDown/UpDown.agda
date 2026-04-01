module UpDown where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_,_)
open import Data.Fin.Subset using (Subset; _∈_; _∉_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)
  renaming (subst to substEq)

open import Types
open import TypeSubst

Label : Set
Label = ℕ

------------------------------------------------------------------------
-- Widening (Up)
------------------------------------------------------------------------

infixr 7 _↦_
infixl 6 _；_
infix 3 _∣_⊢_⊑_
infix 3 _∣_⊢_⊒_

⌊_⌋ : ∀{Ψ} → Seal Ψ → Fin Ψ
⌊_⌋ Zˢ = Fin.zero
⌊_⌋ (Sˢ α) = suc ⌊ α ⌋

⊢_∉_ : ∀{Δ}{Ψ}{G : Ty Δ Ψ} → Ground G → Vec Bool Ψ → Set
⊢ (｀ α) ∉ Φ = ⌊ α ⌋ ∉ Φ
⊢ (‵ ι) ∉ Φ = ⊤
⊢ ★⇒★ ∉ Φ = ⊤

data _∣_⊢_⊑_ {Δ}{Ψ} (Σ : Store Δ Ψ) (Φ : Vec Bool Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
  tag : ∀{G}
    → (g : Ground G)
    → ⊢ g ∉ Φ
    → Label
    → Σ ∣ Φ ⊢ G ⊑ `★

  unseal : ∀{α}{A}
    → Σ ∋ˢ α ⦂ A
    → ⌊ α ⌋ ∈ Φ
    → Σ ∣ Φ ⊢ ｀ α ⊑ A

  _↦_ : ∀{A A′ B B′}
    → Σ ∣ Φ ⊢ A′ ⊑ A
    → Σ ∣ Φ ⊢ B ⊑ B′
    → Σ ∣ Φ ⊢ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ∀ᵖ : ∀{A B : Ty (suc Δ) Ψ}
    → ⟰ᵗ Σ ∣ Φ ⊢ A ⊑ B
    → Σ ∣ Φ ⊢ `∀ A ⊑ `∀ B

  ν_ : ∀{A : Ty (suc Δ) Ψ}{B : Ty Δ Ψ}
    → (Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ ∣ true ∷ Φ ⊢ (⇑ˢ A) [ ｀ Zˢ ]ᵗ ⊑ ⇑ˢ B
    → Σ ∣ Φ ⊢ (`∀ A) ⊑ B

  id : ∀{A}
    → Σ ∣ Φ ⊢ A ⊑ A

  _；_ : ∀{A B C}
    → Σ ∣ Φ ⊢ A ⊑ B
    → Σ ∣ Φ ⊢ B ⊑ C
    → Σ ∣ Φ ⊢ A ⊑ C

------------------------------------------------------------------------
-- Narrowing (Down)
------------------------------------------------------------------------

data _∣_⊢_⊒_ {Δ}{Ψ} (Σ : Store Δ Ψ) (Φ : Vec Bool Ψ) : Ty Δ Ψ → Ty Δ Ψ → Set where
  untag : ∀{G}
    → (g : Ground G)
    → ⊢ g ∉ Φ
    → Label
    → Σ ∣ Φ ⊢ `★ ⊒ G

  seal : ∀{α}{A}
    → Σ ∋ˢ α ⦂ A
    → ⌊ α ⌋ ∈ Φ
    → Σ ∣ Φ ⊢ A ⊒ ｀ α

  _↦_ : ∀{A A′ B B′}
    → Σ ∣ Φ ⊢ A′ ⊑ A
    → Σ ∣ Φ ⊢ B ⊒ B′
    → Σ ∣ Φ ⊢ (A ⇒ B) ⊒ (A′ ⇒ B′)

  ∀ᵖ : ∀{A B : Ty (suc Δ) Ψ}
    → ⟰ᵗ Σ ∣ Φ ⊢ A ⊒ B
    → Σ ∣ Φ ⊢ (`∀ A) ⊒ (`∀ B)

  ν_ : ∀{A : Ty (suc Δ) Ψ}{B : Ty Δ Ψ}
    → (Zˢ , ⇑ˢ `★) ∷ ⟰ˢ Σ ∣ false ∷ Φ ⊢ (⇑ˢ A) [ ｀ Zˢ ]ᵗ ⊒ ⇑ˢ B
    → Σ ∣ Φ ⊢ `∀ A  ⊒  B

  id : ∀{A}
    → Σ ∣ Φ ⊢ A ⊒ A

  _；_ : ∀{A B C}
    → Σ ∣ Φ ⊢ A ⊒ B
    → Σ ∣ Φ ⊢ B ⊒ C
    → Σ ∣ Φ ⊢ A ⊒ C

