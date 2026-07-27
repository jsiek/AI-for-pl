module
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  where

-- File Charter:
--   * Defines the exact residual evidence preserved while a target
--     instantiation allocates a fresh seal and completes its administrative
--     reduction.
--   * Retains the matched pre-allocation body relation, the cast/index
--     creation equation, and the store lineage joining that body world to
--     the final right-extended world.
--   * Accepts the matched body relation as a parameter, so the residual is
--     independent of every particular term-imprecision judgment.
--   * Defines embedded creation residuals from an exact canonical base and
--     composable QTI-free world embeddings.
--   * Does not construct or re-export a term-imprecision edge.

open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Coercions using (Coercion; Inert; ModeEnv; inst)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Imprecision using
  ( ImpAssm
  ; ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴿᵢ
  )
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_; ∀ⁱ_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; StoreImpEntry
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  (No•; Term; Value; renameᵗᵐ; Λ_; _⟨_⟩)
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
open import Types using
  (Renameᵗ; Ty; TyCtx; ★; wf★; `∀; renameᵗ; ⇑ᵗ)
open import proof.Core.Properties.TypeProperties using (TyRenameWf)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (rename-assm²ᵢ; ⊑-renameᵗ²ᵢ; ⊑-target-lift-rightᵢ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)


data StoreImpPrefixᴿ {Φ Δᴸ Δᴿ} :
    StoreImp Φ Δᴸ Δᴿ → StoreImp Φ Δᴸ Δᴿ → Set where
  prefix-reflᴿ : ∀ {ρ} → StoreImpPrefixᴿ ρ ρ

  prefix-∷ᴿ :
    ∀ {ρ₀ ρ⁺} {entry : StoreImpEntry Φ Δᴸ Δᴿ} →
    StoreImpPrefixᴿ ρ₀ ρ⁺ →
    StoreImpPrefixᴿ ρ₀ (entry ∷ ρ⁺)


record TargetInstantiationCreation
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {W W′ : Term} {B C D : Ty} {s : Coercion} {μ : ModeEnv}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ D ⊑ C ⊣ suc Δᴿ}
    {f : Φ ∣ Δᴸ ⊢ `∀ D ⊑ B ⊣ Δᴿ}
    {body-shape : ImprecisionShape}
    (body-relation : Set₁) : Set₁ where
  constructor target-instantiation-creation
  field
    store-prefix : StoreImpPrefixᴿ ρ₀ ρ⁺
    cast-mode : CastMode μ
    seal-mode : SealModeStore★ μ (rightStoreⁱ ρ₀)
    instantiation-typing :
      μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ inst B s ∶ `∀ C ⊑ B
    matched-store-lift :
      LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ∀
    right-store-lift :
      LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ⁺ ρᴿ⁺
    source-body-value : Value W
    source-body-no-bullet : No• W
    target-body-value : Value W′
    target-body-no-bullet : No• W′
    body-cast-inert : Inert s
    matched-body-relation : body-relation
    instantiation-shape :
      widening ⊢ᶜ inst B s ⦂ νˢ body-shape
    index-composition :
      ⌊ ∀ⁱ r ⌋ ； νˢ body-shape ≋ ⌊ f ⌋
    source-result-typing :
      Δᴸ
        ∣ leftStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
        ∣ [] ⊢ Λ W ⦂ `∀ D
    target-result-typing :
      suc Δᴿ
        ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
        ∣ [] ⊢ W′ ⟨ s ⟩ ⦂ ⇑ᵗ B


data EmbeddedTargetInstantiationCreation
    {Φ₀ : ImpCtx} {Θᴸ Θᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
      (suc Θᴸ) (suc Θᴿ)}
    {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
    {W W′ : Term} {B C D : Ty} {s : Coercion} {μ : ModeEnv}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
      ∣ suc Θᴸ ⊢ D ⊑ C ⊣ suc Θᴿ}
    {f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ B ⊣ Θᴿ}
    {body-shape : ImprecisionShape}
    (body-relation : Set₁) :
    ∀ {Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx} →
    StoreImp Ψ Δᴸ Δᴿ →
    (M M′ : Term) → (A A′ : Ty) →
    Ψ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ →
    Set₁ where

  exact-creationᴱ :
    TargetInstantiationCreation
      {Φ = Φ₀} {Δᴸ = Θᴸ} {Δᴿ = Θᴿ}
      {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ⁺}
      {W = W} {W′ = W′} {B = B} {C = C} {D = D}
      {s = s} {μ = μ} {r = r} {f = f}
      {body-shape = body-shape}
      body-relation →
    EmbeddedTargetInstantiationCreation
      {Φ₀ = Φ₀} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
      {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ⁺}
      {W = W} {W′ = W′} {B = B} {C = C} {D = D}
      {s = s} {μ = μ} {r = r} {f = f}
      {body-shape = body-shape}
      body-relation
      (store-right zero ★ wf★ ∷ ρᴿ⁺)
      (Λ W) (W′ ⟨ s ⟩) (`∀ D) (⇑ᵗ B)
      (⊑-target-lift-rightᵢ f)

  embed-creationᴱ :
    ∀ {Ψ Ω Δᴸ Δᴿ Υᴸ Υᴿ ρ ρ′ M M′ A A′ p τ σ} →
    EmbeddedTargetInstantiationCreation
      {Φ₀ = Φ₀} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
      {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ⁺}
      {W = W} {W′ = W′} {B = B} {C = C} {D = D}
      {s = s} {μ = μ} {r = r} {f = f}
      {body-shape = body-shape}
      body-relation
      {Ψ = Ψ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
      ρ M M′ A A′ p →
    (assm : ∀ {a : ImpAssm} →
      a ∈ Ψ → rename-assm²ᵢ τ σ a ∈ Ω) →
    (hτ : TyRenameWf Δᴸ Υᴸ τ) →
    (hσ : TyRenameWf Δᴿ Υᴿ σ) →
    RelStoreEmbeddingⁱ τ σ ρ ρ′ →
    Υᴸ ∣ leftStoreⁱ ρ′ ∣ []
      ⊢ renameᵗᵐ τ M ⦂ renameᵗ τ A →
    Υᴿ ∣ rightStoreⁱ ρ′ ∣ []
      ⊢ renameᵗᵐ σ M′ ⦂ renameᵗ σ A′ →
    EmbeddedTargetInstantiationCreation
      {Φ₀ = Φ₀} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
      {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ⁺}
      {W = W} {W′ = W′} {B = B} {C = C} {D = D}
      {s = s} {μ = μ} {r = r} {f = f}
      {body-shape = body-shape}
      body-relation
      {Ψ = Ω} {Δᴸ = Υᴸ} {Δᴿ = Υᴿ}
      ρ′
      (renameᵗᵐ τ M) (renameᵗᵐ σ M′)
      (renameᵗ τ A) (renameᵗ σ A′)
      (⊑-renameᵗ²ᵢ assm hτ hσ p)
