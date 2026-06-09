module Ctx where

-- File Charter:
--   * Context-focused lemmas: lookup transport and context-map commutation facts.
--   * Theorems whose main subject is `Ctx`, `map` over contexts, or `∋` lookup.
--   * No generic `Ty` substitution algebra and no coercion/store metatheory.
-- Note to self:
--   * If a new lemma is primarily about context structure or context lookup, put it
--     here; otherwise move it to the more specific owning module.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (map; []; _∷_)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (cong₂; sym)

open import Types

------------------------------------------------------------------------
-- Context lookup transport under renaming/substitution
------------------------------------------------------------------------

⤊ᵗ : Ctx → Ctx
⤊ᵗ Γ = map (renameᵗ suc) Γ

------------------------------------------------------------------------
-- Context well-formedness
------------------------------------------------------------------------

CtxWf : TyCtx → Ctx → Set₁
CtxWf Δ Γ = ∀ {x A} → Γ ∋ x ⦂ A → WfTy Δ A

ctxWf-[] : {Δ : TyCtx} → CtxWf Δ []
ctxWf-[] ()

ctxWf-∷ :
  {Δ : TyCtx} {Γ : Ctx} {A : Ty} →
  WfTy Δ A →
  CtxWf Δ Γ →
  CtxWf Δ (A ∷ Γ)
ctxWf-∷ hA hΓ Z = hA
ctxWf-∷ hA hΓ (S h) = hΓ h
