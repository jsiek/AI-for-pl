module Ctx where

-- File Charter:
--   * Typing contexts and well-formedness

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; map; []; _∷_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (cong₂; sym)

open import Types

Ctx = List Ty

⤊ᵗ : Ctx → Ctx
⤊ᵗ Γ = map (renameᵗ suc) Γ

CtxWf : TyCtx → Ctx → Set₁
CtxWf Δ Γ = ∀ {x A} → Γ ∋ x ⦂ A → WfTy Δ A

ctxWf-[] : ∀ {Δ} → CtxWf Δ []
ctxWf-[] ()

ctxWf-∷ : ∀ {Δ Γ A} → WfTy Δ A → CtxWf Δ Γ → CtxWf Δ (A ∷ Γ)
ctxWf-∷ hA hΓ Z = hA
ctxWf-∷ hA hΓ (S h) = hΓ h
