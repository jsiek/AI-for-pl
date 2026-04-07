module intrinsic.Ctx where

open import intrinsic.Types

infixl 5 _,_
infix  4 _∋_

data Ctx (Δ : TyCtx) : Set where
  ∅   : Ctx Δ
  _,_ : Ctx Δ → Type Δ → Ctx Δ

data _∋_ {Δ : TyCtx} : Ctx Δ → Type Δ → Set where
  Z  : ∀ {Γ A} → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → Γ , B ∋ A


renameCtx : ∀ {Δ Δ'} → Δ ⇒ʳ Δ' → Ctx Δ → Ctx Δ'
renameCtx ρ ∅       = ∅
renameCtx ρ (Γ , A)  = renameCtx ρ Γ , renameᵗ ρ A

substCtx : ∀ {Δ Δ'} → Δ ⇒ˢ Δ' → Ctx Δ → Ctx Δ'
substCtx σ ∅       = ∅
substCtx σ (Γ , A) = substCtx σ Γ , substᵗ σ A

renameᵗ-∋ : ∀ {Δ Δ'} (ρ : Δ ⇒ʳ Δ') {Γ : Ctx Δ} {A : Type Δ}
  → Γ ∋ A
  → renameCtx ρ Γ ∋ renameᵗ ρ A
renameᵗ-∋ ρ Z      = Z
renameᵗ-∋ ρ (S x)  = S (renameᵗ-∋ ρ x)

substᵗ-∋ : ∀ {Δ Δ'} (σ : Δ ⇒ˢ Δ') {Γ : Ctx Δ} {A : Type Δ}
  → Γ ∋ A
  → substCtx σ Γ ∋ substᵗ σ A
substᵗ-∋ σ Z      = Z
substᵗ-∋ σ (S x)  = S (substᵗ-∋ σ x)

⇑ᶜ : ∀ {Δ} → Ctx Δ → Ctx (Δ ,α)
⇑ᶜ = renameCtx S_
