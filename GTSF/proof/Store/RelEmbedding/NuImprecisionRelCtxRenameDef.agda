module
  proof.Store.RelEmbedding.NuImprecisionRelCtxRenameDef
  where

-- File Charter:
--   * Defines structural two-sided renaming of relational term contexts.
--   * Retains the exact renamed endpoint-imprecision proof in every entry.
--   * Is independent of term imprecision, simulation, catch-up, and
--     quotiented-term relations.
--   * Contains no implementation theorem, postulate, hole, permissive option,
--     termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

open import NuTermImprecision using
  (CtxImp; ctx-imp)
open import Types using
  (Renameᵗ; renameᵗ)
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using
  (rename-assm²ᵢ; ⊑-rename-at²ᵢ)


data RelCtxRenameⁱ
    {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ}
    (τ σ : Renameᵗ)
    (assm : ∀ {a} → a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ)
    (hτ : TyRenameWf Δᴸ Θᴸ τ)
    (hσ : TyRenameWf Δᴿ Θᴿ σ) :
    CtxImp Φ Δᴸ Δᴿ → CtxImp Ψ Θᴸ Θᴿ → Set₁ where
  rel-ctx-rename-[] :
    RelCtxRenameⁱ τ σ assm hτ hσ [] []

  rel-ctx-rename-∷ :
    ∀ {γ γ′ A A′ B B′ p} →
    (eqA : A′ ≡ renameᵗ τ A) →
    (eqB : B′ ≡ renameᵗ σ B) →
    RelCtxRenameⁱ τ σ assm hτ hσ γ γ′ →
    RelCtxRenameⁱ τ σ assm hτ hσ
      (ctx-imp A B p ∷ γ)
      (ctx-imp A′ B′
        (⊑-rename-at²ᵢ assm hτ hσ eqA eqB p) ∷ γ′)
