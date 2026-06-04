module ImprecisionAlt where

-- File Charter:
--   * Imprecision on types (alternative design to the one in Imprecision.agda)

open import Types
open import ConsistencyAlt using (CAssm; CCtx; _~ᶜ★; ★~ᶜ_; _~ᶜ_)

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; _<_; zero; suc; z<s; s<s)
open import Data.Product using
  (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (cong)

data ImpAssm : Set where
  _ˣ⊑★ : TyVar → ImpAssm
  _ˣ⊑ˣ_ : TyVar → TyVar → ImpAssm

ImpCtx : Set
ImpCtx = List ImpAssm

⇑ᵢₐ : ImpAssm → ImpAssm
⇑ᵢₐ (X ˣ⊑★) = suc X ˣ⊑★
⇑ᵢₐ (X ˣ⊑ˣ Y) = suc X ˣ⊑ˣ suc Y

⇑ᴸᵢₐ : ImpAssm → ImpAssm
⇑ᴸᵢₐ (X ˣ⊑★) = suc X ˣ⊑★
⇑ᴸᵢₐ (X ˣ⊑ˣ Y) = suc X ˣ⊑ˣ Y

⇑ᵢ : ImpCtx → ImpCtx
⇑ᵢ [] = []
⇑ᵢ (m ∷ Φ) = ⇑ᵢₐ m ∷ ⇑ᵢ Φ

⇑ᴸᵢ : ImpCtx → ImpCtx
⇑ᴸᵢ [] = []
⇑ᴸᵢ (m ∷ Φ) = ⇑ᴸᵢₐ m ∷ ⇑ᴸᵢ Φ

infix 4 _∣_⊢_⊑_
data _∣_⊢_⊑_ (Ψ : SealCtx) (Φ : ImpCtx) : Ty → Ty → Set where
  id★ :
    -------------
    Ψ ∣ Φ ⊢ ★ ⊑ ★

  idˣ : ∀ {X Y}
    → (X ˣ⊑ˣ Y) ∈ Φ
    ---------------------
    → Ψ ∣ Φ ⊢ ＇ X ⊑ ＇ Y
    
  idι : ∀ {ι}
    -------------------
    → Ψ ∣ Φ ⊢ ‵ ι ⊑ ‵ ι

  idα : ∀ {α}
    → WfTy (length Φ) Ψ (｀ α)
    --------------------------
    → Ψ ∣ Φ ⊢ ｀ α ⊑ ｀ α

  _↦_ : ∀ {A A′ B B′} →
    Ψ ∣ Φ ⊢ A ⊑ A′ →
    Ψ ∣ Φ ⊢ B ⊑ B′ →
    ---------------------------
    Ψ ∣ Φ ⊢ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ∀ⁱ_ : ∀ {A B}
    → Ψ ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ ⊢ A ⊑ B
    ----------------------------
    → Ψ ∣ Φ ⊢ (`∀ A) ⊑ (`∀ B)

  tag_ : ∀ (ι : Base)
    → Ψ ∣ Φ ⊢ ‵ ι ⊑ ★

  tag_⇒_ : ∀ {A₁ A₂}
    → Ψ ∣ Φ ⊢ A₁ ⊑ ★
    → Ψ ∣ Φ ⊢ A₂ ⊑ ★
    ---------------------
    → Ψ ∣ Φ ⊢ A₁ ⇒ A₂ ⊑ ★

  tagˣ_ : ∀ {X}
    → X ˣ⊑★ ∈ Φ
    ------------------
    → Ψ ∣ Φ ⊢ ＇ X ⊑ ★

  ν : ∀ {A B}
    → occurs zero A ≡ true
    → Ψ ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ ⊢ A ⊑ B
    -------------------------
    → Ψ ∣ Φ ⊢ (`∀ A) ⊑ B


------------------------------------------------------------------------
-- Greatest Lower Bound
------------------------------------------------------------------------

CommonLowerᶜ : ImpCtx → ImpCtx → Ty → Ty → Ty → Set
CommonLowerᶜ Φᴸ Φᴿ C A B =
  0 ∣ Φᴸ ⊢ C ⊑ A × 0 ∣ Φᴿ ⊢ C ⊑ B

CommonLower : Ty → Ty → Set
CommonLower A B = Σ[ C ∈ Ty ] CommonLowerᶜ [] [] C A B

_⊢_＝_⊓_ : SealCtx → Ty → Ty → Ty → Set
_⊢_＝_⊓_ Ψ A B C = Ψ ∣ [] ⊢ A ⊑ B × Ψ ∣ [] ⊢ A ⊑ C
    × (∀ A′ → Ψ ∣ [] ⊢ A′ ⊑ B → Ψ ∣ [] ⊢ A′ ⊑ C
        → Ψ ∣ [] ⊢ A′ ⊑ A)
