module proof.NuImprecisionLeftWorldInsertionDef where

-- File Charter:
--   * Defines proof-relevant world traversal for a canonical source-side
--     type-name insertion.
--   * Preserves the exact renaming, source world, target world, and
--     assumption-map shapes under matched, source-left, and target-right
--     binder lifts.
--   * Contains no term relation, simulation result, implementation handler,
--     postulate, hole, or permissive option.

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc)

open import ImprecisionWf using
  ( ImpCtx
  ; ⇑ᴿᵢ
  )
open import Types using (Renameᵗ; extᵗ)
open import proof.MaximalLowerBoundsWf using
  ( ∀ᵢᶜ
  ; νᵢᶜ
  ; rename-assm²ᵢ
  ; rename-assm²-⇑ᴸᵢ
  ; rename-assm²-source-νᵢ
  )
open import proof.NuImprecisionSimulationCore using
  ( rename-assm²-∀-leftᵢ
  ; rename-assm²-⇑ᴿᵢ
  )


data LeftWorldInsertionⁱ :
    (τ : Renameᵗ) →
    (Φ Ψ : ImpCtx) →
    (∀ {a} → a ∈ Φ →
      rename-assm²ᵢ τ (λ X → X) a ∈ Ψ) →
    Set where

  left-world-sourceⁱ :
    ∀ {Φ} →
    LeftWorldInsertionⁱ
      suc Φ (νᵢᶜ Φ) rename-assm²-source-νᵢ

  left-world-matched-allⁱ :
    ∀ {τ Φ Ψ}
      {assm : ∀ {a} → a ∈ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ Ψ} →
    LeftWorldInsertionⁱ τ Φ Ψ assm →
    LeftWorldInsertionⁱ
      (extᵗ τ) (∀ᵢᶜ Φ) (∀ᵢᶜ Ψ)
      (rename-assm²-∀-leftᵢ assm)

  left-world-source-leftⁱ :
    ∀ {τ Φ Ψ}
      {assm : ∀ {a} → a ∈ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ Ψ} →
    LeftWorldInsertionⁱ τ Φ Ψ assm →
    LeftWorldInsertionⁱ
      (extᵗ τ) (νᵢᶜ Φ) (νᵢᶜ Ψ)
      (rename-assm²-⇑ᴸᵢ assm)

  left-world-target-rightⁱ :
    ∀ {τ Φ Ψ}
      {assm : ∀ {a} → a ∈ Φ →
        rename-assm²ᵢ τ (λ X → X) a ∈ Ψ} →
    LeftWorldInsertionⁱ τ Φ Ψ assm →
    LeftWorldInsertionⁱ
      τ (⇑ᴿᵢ Φ) (⇑ᴿᵢ Ψ)
      (rename-assm²-⇑ᴿᵢ assm)
