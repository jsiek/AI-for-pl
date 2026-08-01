module TermCtx where

-- File Charter:
--   * Intrinsically well-scoped term-variable typing contexts.
--   * Lookup and its transport under type renaming and substitution.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (suc)

open import Types

TermCtx : TyCtx → Set
TermCtx Δ = List (Ty Δ)

infix 4 _∋_⦂_

data _∋_⦂_ {Δ : TyCtx} : TermCtx Δ → ℕ → Ty Δ → Set where
  Z : ∀ {Γ A}
      -----------------
    → (A ∷ Γ) ∋ zero ⦂ A

  S : ∀ {Γ A B x}
    → Γ ∋ x ⦂ A
      -------------------
    → (B ∷ Γ) ∋ suc x ⦂ A

renameCtx : ∀ {Δ Δ′} → Δ ⇒ʳ Δ′ → TermCtx Δ → TermCtx Δ′
renameCtx ρ [] = []
renameCtx ρ (A ∷ Γ) = renameᵗ ρ A ∷ renameCtx ρ Γ

substCtx : ∀ {Δ Δ′} → Δ ⇒ˢ Δ′ → TermCtx Δ → TermCtx Δ′
substCtx σ [] = []
substCtx σ (A ∷ Γ) = substᵗ σ A ∷ substCtx σ Γ

renameᵗ-∋ : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {Γ : TermCtx Δ}
    {x : ℕ} {A : Ty Δ}
  → Γ ∋ x ⦂ A
  → renameCtx ρ Γ ∋ x ⦂ renameᵗ ρ A
renameᵗ-∋ ρ Z = Z
renameᵗ-∋ ρ (S x) = S (renameᵗ-∋ ρ x)

substᵗ-∋ : ∀ {Δ Δ′} (σ : Δ ⇒ˢ Δ′) {Γ : TermCtx Δ}
    {x : ℕ} {A : Ty Δ}
  → Γ ∋ x ⦂ A
  → substCtx σ Γ ∋ x ⦂ substᵗ σ A
substᵗ-∋ σ Z = Z
substᵗ-∋ σ (S x) = S (substᵗ-∋ σ x)

⇑ᶜ : ∀ {Δ} → TermCtx Δ → TermCtx (suc Δ)
⇑ᶜ = renameCtx suc
