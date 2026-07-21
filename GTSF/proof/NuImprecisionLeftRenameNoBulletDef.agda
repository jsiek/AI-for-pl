module proof.NuImprecisionLeftRenameNoBulletDef where

-- File Charter:
--   * Defines generic left-only renaming of ordinary and quotiented QTI
--     derivations whose source and target terms contain no runtime bullet.
--   * Bundles the mutually implemented maps while returning relation
--     derivations directly.
--   * Contains no implementation, postulate, hole, permissive option, or
--     result, path, or outcome carrier.

open import Data.List.Membership.Propositional using (_∈_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuTermImprecision using
  ( CtxImp
  ; StoreImp
  )
open import NuTerms using
  ( No•
  ; Term
  ; renameᵗᵐ
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Renameᵗ; Ty; TyCtx; renameᵗ)
open import proof.MaximalLowerBoundsWf using (rename-assm²ᵢ)
open import proof.NuImprecisionSimulationCore using
  ( LeftCtxRenameⁱ
  ; LeftStoreRenameⁱ
  ; ⊑-rename-leftᵢ
  ; ⊑ᵖ-rename-leftᵢ
  )
open import proof.TypeProperties using (TyRenameWf)


record LeftRenameNoBullet : Set₁ where
  field
    left-rename-no•ᵀ :
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
      LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
      LeftCtxRenameⁱ τ assm hτ γ γ′ →
      No• M →
      No• M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
      Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
        ⊢ᴺ renameᵗᵐ τ M ⊑ M′
        ⦂ renameᵗ τ A ⊑ B
        ∶ ⊑-rename-leftᵢ τ assm hτ p

    left-rename-no•ᵀᵖ :
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
      LeftStoreRenameⁱ τ assm hτ ρ ρ′ →
      LeftCtxRenameⁱ τ assm hτ γ γ′ →
      No• M →
      No• M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
      Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
        ⊢ᴺᵖ renameᵗᵐ τ M ⊑ M′
        ⦂ renameᵗ τ D ⊑ᵖ D′
        ∶ ⊑ᵖ-rename-leftᵢ τ assm hτ q

open LeftRenameNoBullet public
