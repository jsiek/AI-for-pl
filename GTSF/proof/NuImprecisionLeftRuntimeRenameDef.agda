module proof.NuImprecisionLeftRuntimeRenameDef where

-- File Charter:
--   * Defines structural left-insertion transport for ordinary and
--     quotiented Nu-term imprecision with a bullet-free source.
--   * Bundles the mutually implemented maps while returning direct relation
--     derivations, with no simulation result or outcome wrapper.
--   * Requires structural world-insertion evidence so target-right runtime
--     allocation branches expose their exact lifted world and map shapes.
--   * Contains no implementation, postulate, hole, permissive option, or
--     source-allocation index specialization.

open import Data.List.Membership.Propositional using (_∈_)

open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using (CtxImp; StoreImp)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; renameᵗᵐ
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Renameᵗ; Ty; TyCtx; renameᵗ)
open import proof.MaximalLowerBoundsWf using (rename-assm²ᵢ)
open import proof.NuImprecisionLeftWorldInsertionDef using
  (LeftWorldInsertionⁱ)
open import proof.NuImprecisionSimulationCore using
  ( LeftCtxRenameⁱ
  ; LeftInsertion
  ; LeftStoreRenameⁱ
  ; ⊑-rename-leftᵢ
  ; ⊑ᵖ-rename-leftᵢ
  )
open import proof.TypeProperties using (TyRenameWf)


record LeftRuntimeRename : Set₁ where
  field
    left-runtime-renameᵀ :
      ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ : TyCtx} {τ : Renameᵗ}
        {assm : ∀ {a} → a ∈ Φ →
          rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
        {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
        {γ : CtxImp Φ Δᴸ Δᴿ}
        {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
        {M M′ : Term} {A B : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      LeftInsertion τ →
      LeftWorldInsertionⁱ τ Φ Ψ assm →
      LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
      LeftCtxRenameⁱ τ assm hτ γ γ′ →
      No• M →
      RuntimeOK M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
      Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
        ⊢ᴺ renameᵗᵐ τ M ⊑ M′
        ⦂ renameᵗ τ A ⊑ B ∶ ⊑-rename-leftᵢ τ assm hτ p

    left-runtime-renameᵀᵖ :
      ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ : TyCtx} {τ : Renameᵗ}
        {assm : ∀ {a} → a ∈ Φ →
          rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
        {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
        {γ : CtxImp Φ Δᴸ Δᴿ}
        {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
        {M M′ : Term} {D D′ : Ty}
        {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
      LeftInsertion τ →
      LeftWorldInsertionⁱ τ Φ Ψ assm →
      LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
      LeftCtxRenameⁱ τ assm hτ γ γ′ →
      No• M →
      RuntimeOK M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
      Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
        ⊢ᴺᵖ renameᵗᵐ τ M ⊑ M′
        ⦂ renameᵗ τ D ⊑ᵖ D′ ∶ ⊑ᵖ-rename-leftᵢ τ assm hτ q

open LeftRuntimeRename public
