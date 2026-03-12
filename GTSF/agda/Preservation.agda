module Preservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_; [])
open import Data.Nat using (zero; suc)
open import Data.Empty using (⊥; ⊥-elim)

open import PolyCoercions
open import PolyCastCalculus

------------------------------------------------------------------------
-- Typing implies type well-formedness
------------------------------------------------------------------------

postulate
  typing-wfty : ∀ {Σ Δ Γ M A}
    → Σ ∣ Δ ⊢ Γ ⊢ M ⦂ A
    → WfTy Δ Σ A

------------------------------------------------------------------------
-- Term substitution preserves typing (closed-world variant)
------------------------------------------------------------------------

postulate
  typing-single-subst : ∀ {Σ A B N V}
    → Σ ∣ zero ⊢ (A ∷ []) ⊢ N ⦂ B
    → Σ ∣ zero ⊢ [] ⊢ V ⦂ A
    → Σ ∣ zero ⊢ [] ⊢ N [ V ]ᴹ ⦂ B

  impossible-βδ : ∀ {Σ A k₁ k₂}
    → Σ ∣ zero ⊢ [] ⊢ ($k k₁ · $k k₂) ⦂ A
    → ⊥

  preserve-β-ty★-plain : ∀ {Σ M A A₀}
    → Σ ∣ zero ⊢ [] ⊢ ((Λ M ⦂ A₀) ·[ `★ ]) ⦂ A
    → Σ ∣ zero ⊢ [] ⊢ (M [ `★ ]ᵀ) ⦂ A

  preserve-β-ty-wrap★ : ∀ {Σ V c A}
    → Value V
    → Σ ∣ zero ⊢ [] ⊢ ((V ⟨ ∀ᶜ c ⟩) ·[ `★ ]) ⦂ A
    → Σ ∣ zero ⊢ [] ⊢ ((V ·[ `★ ]) ⟨ substᶜᵗ (singleTyEnv `★) c ⟩) ⦂ A

  preserve-β-ty-plain : ∀ {Σ M A A₀ B}
    → NonDyn B
    → Σ ∣ zero ⊢ [] ⊢ ((Λ M ⦂ A₀) ·[ B ]) ⦂ A
    → extendStore Σ B ∣ zero ⊢ [] ⊢
        ((M [ `U (fresh Σ) ]ᵀ) ⟨ coerce⁺ (fresh Σ) (A₀ [ `U (fresh Σ) ]ᵗ) ⟩) ⦂ A

  preserve-β-ty-wrap : ∀ {Σ V A A₀ Aₙ c B}
    → NonDyn B
    → Value V
    → Σ ∣ zero ⊢ ∀ᶜ c ⦂ `∀ A₀ ⇨ `∀ Aₙ
    → Σ ∣ zero ⊢ [] ⊢ ((V ⟨ ∀ᶜ c ⟩) ·[ B ]) ⦂ A
    → extendStore Σ B ∣ zero ⊢ [] ⊢
        (((V ·[ `U (fresh Σ) ]) ⟨ substᶜᵗ (singleTyEnv (`U (fresh Σ))) c ⟩)
          ⟨ coerce⁺ (fresh Σ) (Aₙ [ `U (fresh Σ) ]ᵗ) ⟩) ⦂ A

------------------------------------------------------------------------
-- Blame under frames
------------------------------------------------------------------------

frame-blame : ∀ {Σ F p A}
  → Σ ∣ zero ⊢ [] ⊢ plug F (blame p) ⦂ A
  → Σ ∣ zero ⊢ [] ⊢ blame p ⦂ A
frame-blame h = ⊢blame (typing-wfty h)

∋ᵁ-unique : ∀ {Σ U A B}
  → Σ ∋ᵁ U ⦂ A
  → Σ ∋ᵁ U ⦂ B
  → A ≡ B
∋ᵁ-unique Zᵁ Zᵁ = refl
∋ᵁ-unique (Sᵁ hA) (Sᵁ hB) = ∋ᵁ-unique hA hB

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

mutual
  preservation : ∀ {Σ Σ′ M N A}
    → Σ ∣ zero ⊢ [] ⊢ M ⦂ A
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → Σ′ ∣ zero ⊢ [] ⊢ N ⦂ A
  preservation M⦂ (ξξ {F = F} refl refl M→N) =
    frame-preservation {F = F} M⦂ M→N
  preservation M⦂ β-δ with impossible-βδ M⦂
  ... | ()
  preservation (⊢· {A = A} (⊢ƛ {A = A} hA hN) hV) (β-ƛ vV) =
    typing-single-subst hN hV
  preservation (⊢⟨⟩ hV (⊢idᶜ _ _)) (β-id vV) = hV
  preservation (⊢· (⊢⟨⟩ hV (⊢↦ cwt dwt)) hW) (β-↦ vV vW) =
    ⊢⟨⟩ (⊢· hV (⊢⟨⟩ hW cwt)) dwt
  preservation (⊢⟨⟩ (⊢⟨⟩ hV (⊢! _ _ _)) (⊢? _ _ _)) (β-proj-inj-ok vV) = hV
  preservation (⊢⟨⟩ (⊢⟨⟩ hV (⊢! _ _ _)) (⊢? _ hG _)) (β-proj-inj-bad vV G≢H) =
    ⊢blame hG
  preservation (⊢⟨⟩ (⊢⟨⟩ hV (⊢conceal _ hU₁)) (⊢reveal _ hU₂)) (β-remove vV)
    with ∋ᵁ-unique hU₁ hU₂
  ... | refl = hV
  preservation (⊢⟨⟩ hV (⊢⨟ cwt dwt)) (β-seq vV) =
    ⊢⟨⟩ (⊢⟨⟩ hV cwt) dwt
  preservation (⊢⟨⟩ hV (⊢⊥ _ _ hB)) (β-fail vV) =
    ⊢blame hB
  preservation M⦂ β-ty★-plain = preserve-β-ty★-plain M⦂
  preservation M⦂ (β-ty-wrap★ vV) = preserve-β-ty-wrap★ vV M⦂
  preservation (⊢·[] (⊢⟨⟩ (⊢Λ hM) (⊢∀ᶜ cwt)) hB) β-ty★ = {!!}
  preservation M⦂ (β-ty-plain ndB) = preserve-β-ty-plain ndB M⦂
  preservation M⦂ (β-ty-wrap ndB vV cwt) = preserve-β-ty-wrap ndB vV cwt M⦂
  preservation (⊢·[] (⊢⟨⟩ (⊢Λ hM) (⊢∀ᶜ cwt)) hB) (β-ty ndB cwt0) = {!!}
  preservation M⦂ (ξξ-blame {F = F} refl) =
    frame-blame {F = F} M⦂

  frame-preservation : ∀ {F Σ Σ′ M N A}
    → Σ ∣ zero ⊢ [] ⊢ plug F M ⦂ A
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → Σ′ ∣ zero ⊢ [] ⊢ plug F N ⦂ A
  frame-preservation M⦂ M→N = {!!}
