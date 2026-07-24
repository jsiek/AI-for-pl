module
  proof.Target.Administration.NuImprecisionTargetUniversalFusionSpineDef
  where

-- File Charter:
--   * Defines the constructor-form spine of recursively nested universal
--     target-instantiation fusion frames.
--   * Retains one matched-lambda base, every fused frame's generic origin
--     index, and its arbitrary final precision index.
--   * States the fold from the spine back to quotiented term imprecision.
--   * Contains no extraction, normalization, world-coherent result, proof,
--     postulate, hole, permissive option, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Imprecision using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴿᵢ
  )
open import ImprecisionWf using
  ( ImpAssm
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( LiftCtxⁱ
  ; LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  ( Closedᵐ
  ; No•
  ; Term
  ; Value
  ; Λ_
  ; _⟨_⟩
  ; renameᵗᵐ
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import
  proof.Core.Properties.TypeProperties
  using (TyRenameWf)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using (rename-assm²ᵢ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)
open import TermTyping using
  ( CastMode
  ; SealModeStore★
  ; _∣_∣_⊢_⦂_
  )
open import Types using
  ( Renameᵗ
  ; Ty
  ; TyCtx
  ; renameᵗ
  ; wf★
  ; ★
  ; `∀
  ; ⇑ᵗ
  )


data TargetUniversalFusionSpine
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    (ρ : StoreImp Φ Δᴸ Δᴿ) :
    (M M′ : Term) → (A H : Ty) →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ H ⊣ Δᴿ) →
    Set₁ where

  fusion-base :
      ∀ {ρ∀ V V′ D F r} →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
    LiftCtxⁱ {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) [] [] →
    Value V →
    No• V →
    Value V′ →
    No• V′ →
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
      ⊢ᴺ V ⊑ V′ ⦂ D ⊑ F ∶ r →
    TargetUniversalFusionSpine ρ
      (Λ V) (Λ V′) (`∀ D) F (∀ⁱ r)

  fusion-step :
      ∀ {Φ₀ : ImpCtx} {Θᴸ Θᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
        {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
          (suc Θᴸ) (suc Θᴿ)}
        {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
        {τ σ : Renameᵗ}
        {W W′ M M′ : Term}
        {A D E F H : Ty}
        {c : C.Coercion} {μ : C.ModeEnv} {r} →
    StoreImpPrefix ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Θᴿ ∣ rightStoreⁱ ρ₀
      ⊢ C.inst (`∀ E) (C.`∀ c) ∶ `∀ (`∀ F) ⊑ `∀ E →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀) ρ₀ ρ∀ →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ₀) ρ⁺ ρᴿ⁺ →
    Value W →
    No• W →
    Value W′ →
    No• W′ →
    C.Inert (C.`∀ c) →
    TargetUniversalFusionSpine ρ∀ W W′ D F r →
    (f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ `∀ E ⊣ Θᴿ) →
    (assm :
      ∀ {a : ImpAssm} → a ∈ ⇑ᴿᵢ Φ₀ →
        rename-assm²ᵢ τ σ a ∈ Φ) →
    (hτ : TyRenameWf Θᴸ Δᴸ τ) →
    (hσ : TyRenameWf (suc Θᴿ) Δᴿ σ) →
    RelStoreEmbeddingⁱ τ σ
      (store-right zero ★ wf★ ∷ ρᴿ⁺) ρ →
    renameᵗᵐ τ (Λ W) ≡ M →
    renameᵗᵐ σ (W′ ⟨ C.`∀ c ⟩) ≡ M′ →
    renameᵗ τ (`∀ D) ≡ A →
    renameᵗ σ (⇑ᵗ (`∀ E)) ≡ `∀ H →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ H ⊣ Δᴿ) →
    Value M →
    No• M →
    Closedᵐ M →
    Value M′ →
    No• M′ →
    Closedᵐ M′ →
    Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A →
    Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ `∀ H →
    TargetUniversalFusionSpine ρ M M′ A H p


TargetUniversalFusionSpineRelationᵀ : Set₁
TargetUniversalFusionSpineRelationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A H : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ H ⊣ Δᴿ} →
  TargetUniversalFusionSpine ρ M M′ A H p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ `∀ H ∶ p
