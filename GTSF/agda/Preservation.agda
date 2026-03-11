module Preservation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_; [])
open import Data.Nat using (zero; suc)

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

------------------------------------------------------------------------
-- Blame under frames
------------------------------------------------------------------------

frame-blame : ∀ {Σ F p A}
  → Σ ∣ zero ⊢ [] ⊢ plug F (blame p) ⦂ A
  → Σ ∣ zero ⊢ [] ⊢ blame p ⦂ A
frame-blame h = ⊢blame (typing-wfty h)

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

mutual
  preservation : ∀ {Σ Σ′ M N A}
    → Σ ∣ zero ⊢ [] ⊢ M ⦂ A
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → Σ′ ∣ zero ⊢ [] ⊢ N ⦂ A
  preservation M⦂ (ξξ {F = F} refl refl M→N) = {!!}
  preservation M⦂ β-δ = {!!}
  preservation (⊢· {A = A} (⊢ƛ {A = A} hA hN) hV) (β-ƛ vV) =
    typing-single-subst hN hV
  preservation (⊢⟨⟩ hV (⊢idᶜ _ _)) (β-id vV) = hV
  preservation (⊢· (⊢⟨⟩ hV (⊢↦ cwt dwt)) hW) (β-↦ vV vW) =
    ⊢⟨⟩ (⊢· hV (⊢⟨⟩ hW cwt)) dwt
  preservation (⊢⟨⟩ (⊢⟨⟩ hV (⊢! _ _ _)) (⊢? _ _ _)) (β-proj-inj-ok vV) = hV
  preservation (⊢⟨⟩ (⊢⟨⟩ hV (⊢! _ _ _)) (⊢? _ hG _)) (β-proj-inj-bad vV G≢H) =
    ⊢blame hG
  preservation (⊢⟨⟩ (⊢⟨⟩ hV (⊢conceal _ _)) (⊢reveal _ _)) (β-remove vV) = {!!}
  preservation (⊢⟨⟩ hV (⊢⨟ cwt dwt)) (β-seq vV) =
    ⊢⟨⟩ (⊢⟨⟩ hV cwt) dwt
  preservation (⊢⟨⟩ hV (⊢⊥ _ _ hB)) (β-fail vV) =
    ⊢blame hB
  preservation (⊢·[] (⊢⟨⟩ (⊢Λ hM) (⊢∀ᶜ cwt)) hB) β-ty★ = {!!}
  preservation (⊢·[] (⊢⟨⟩ (⊢Λ hM) (⊢∀ᶜ cwt)) hB) (β-ty ndB cwt0) = {!!}
  preservation M⦂ (ξξ-blame {F = F} refl) =
    frame-blame {F = F} M⦂

  frame-preservation : ∀ {F Σ Σ′ M N A}
    → Σ ∣ zero ⊢ [] ⊢ plug F M ⦂ A
    → (Σ ⊲ M) —→ (Σ′ ⊲ N)
    → Σ′ ∣ zero ⊢ [] ⊢ plug F N ⦂ A
  frame-preservation M⦂ M→N = {!!}
