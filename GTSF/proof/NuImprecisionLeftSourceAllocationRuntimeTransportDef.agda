module proof.NuImprecisionLeftSourceAllocationRuntimeTransportDef where

-- File Charter:
--   * Defines runtime-safe QTI transport across the canonical source
--     allocation lift.
--   * Bundles the mutually implemented ordinary and quotient maps while
--     returning relation derivations directly.
--   * Uses canonical left-renaming witnesses and the relation derivation
--     instead of an ambiguous lift or parallel world-path datatype.
--   * Contains no implementation, postulate, hole, permissive option, or
--     result carrier.

open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Data.Nat using (suc)
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
  ; RuntimeOK
  ; Term
  ; renameᵗᵐ
  )
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import Types using (Ty; TyCtx; renameᵗ)
open import proof.MaximalLowerBoundsWf using
  ( νᵢᶜ
  ; rename-assm²-source-νᵢ
  )
open import proof.NuImprecisionSimulationCore using
  ( LeftCtxRenameⁱ
  ; LeftStoreRenameⁱ
  ; ⊑-rename-leftᵢ
  ; ⊑ᵖ-rename-leftᵢ
  )
open import proof.TypeProperties using (TyRenameWf-suc)


record LeftSourceAllocationRuntimeTransport : Set₁ where
  field
    left-source-allocation-runtimeᵀ :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {ρᴸ : StoreImp (νᵢᶜ Φ) (suc Δᴸ) Δᴿ}
        {γ : CtxImp Φ Δᴸ Δᴿ}
        {γᴸ : CtxImp (νᵢᶜ Φ) (suc Δᴸ) Δᴿ}
        {M M′ : Term} {A B : Ty}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
      LeftStoreRenameⁱ suc rename-assm²-source-νᵢ
        TyRenameWf-suc ρ ρᴸ →
      LeftCtxRenameⁱ suc rename-assm²-source-νᵢ
        TyRenameWf-suc γ γᴸ →
      No• M →
      RuntimeOK M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
      νᵢᶜ Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ γᴸ
        ⊢ᴺ renameᵗᵐ suc M ⊑ M′
        ⦂ renameᵗ suc A ⊑ B
        ∶ ⊑-rename-leftᵢ
          suc rename-assm²-source-νᵢ TyRenameWf-suc p

    left-source-allocation-runtimeᵀᵖ :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ : StoreImp Φ Δᴸ Δᴿ}
        {ρᴸ : StoreImp (νᵢᶜ Φ) (suc Δᴸ) Δᴿ}
        {γ : CtxImp Φ Δᴸ Δᴿ}
        {γᴸ : CtxImp (νᵢᶜ Φ) (suc Δᴸ) Δᴿ}
        {M M′ : Term} {D D′ : Ty}
        {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
      LeftStoreRenameⁱ suc rename-assm²-source-νᵢ
        TyRenameWf-suc ρ ρᴸ →
      LeftCtxRenameⁱ suc rename-assm²-source-νᵢ
        TyRenameWf-suc γ γᴸ →
      No• M →
      RuntimeOK M′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺᵖ M ⊑ M′ ⦂ D ⊑ᵖ D′ ∶ q →
      νᵢᶜ Φ ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ γᴸ
        ⊢ᴺᵖ renameᵗᵐ suc M ⊑ M′
        ⦂ renameᵗ suc D ⊑ᵖ D′
        ∶ ⊑ᵖ-rename-leftᵢ
          suc rename-assm²-source-νᵢ TyRenameWf-suc q

open LeftSourceAllocationRuntimeTransport public
