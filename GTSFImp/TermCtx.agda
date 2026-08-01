module TermCtx where

-- File Charter:
--   * Typing contexts and well-formedness

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; map; []; _∷_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (cong₂; sym)

open import Types

TermCtx = List Ty

⤊ᵗ : TermCtx → TermCtx
⤊ᵗ Γ = map (renameᵗ suc) Γ

TermCtxWf : TyCtx → TermCtx → Set₁
TermCtxWf Δ Γ = ∀ {x A} → Γ ∋ x ⦂ A → WfTy Δ A

ctxWf-[] : ∀ {Δ} → TermCtxWf Δ []
ctxWf-[] ()

ctxWf-∷ : ∀ {Δ Γ A} → WfTy Δ A → TermCtxWf Δ Γ → TermCtxWf Δ (A ∷ Γ)
ctxWf-∷ hA hΓ Z = hA
ctxWf-∷ hA hΓ (S h) = hΓ h
