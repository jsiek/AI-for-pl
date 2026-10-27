module CompileInvariants where

-- File Charter:
--   * The context invariants under which elaboration (Compile.agda)
--     preserves typing and precision (CompileMeta.agda).
--   * WfCtx n Γ: every type in the term context Γ is well formed with n
--     type variables in scope.
--   * Δ⊑ ⦂ Δ ⊑ᵉ Δ′: the precision type context Δ⊑ relates the two type
--     contexts entry by entry: abstract to abstract, and knownᵖ q to
--     known B and known B′ where q : B ⊑ B′ in the outer context.
--   * n ⊢ Γ⊑ ⦂ Γ ⊑ᶜ Γ′: each precision derivation in Γ⊑ relates the
--     corresponding entries of Γ and Γ′.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)

open import Types
open import Typing using (Ctx)
open import TermPrecision using (PEnv; PCtx; absᵖ; knownᵖ; psize)

data WfCtx (n : ℕ) : Ctx → Set where
  wfc[] : WfCtx n []
  wfc∷ : ∀ {A Γ} → WfTy n A → WfCtx n Γ → WfCtx n (A ∷ Γ)

infix 4 _⦂_⊑ᵉ_ _⊢_⦂_⊑ᶜ_

data _⦂_⊑ᵉ_ : PEnv → TyEnv → TyEnv → Set where
  ⊑ᵉ[] : [] ⦂ [] ⊑ᵉ []

  ⊑ᵉabs : ∀ {Δ⊑ Δ Δ′} →
    Δ⊑ ⦂ Δ ⊑ᵉ Δ′ →
    (absᵖ ∷ Δ⊑) ⦂ (abs ∷ Δ) ⊑ᵉ (abs ∷ Δ′)

  ⊑ᵉknown : ∀ {Δ⊑ Δ Δ′ q B B′} →
    psize Δ⊑ ⊢ q ⦂ B ⊑ B′ →
    Δ⊑ ⦂ Δ ⊑ᵉ Δ′ →
    (knownᵖ q ∷ Δ⊑) ⦂ (known B ∷ Δ) ⊑ᵉ (known B′ ∷ Δ′)

data _⊢_⦂_⊑ᶜ_ (n : ℕ) : PCtx → Ctx → Ctx → Set where
  ⊑ᶜ[] : n ⊢ [] ⦂ [] ⊑ᶜ []

  ⊑ᶜ∷ : ∀ {Γ⊑ Γ Γ′ p A A′} →
    n ⊢ p ⦂ A ⊑ A′ →
    n ⊢ Γ⊑ ⦂ Γ ⊑ᶜ Γ′ →
    n ⊢ (p ∷ Γ⊑) ⦂ (A ∷ Γ) ⊑ᶜ (A′ ∷ Γ′)
