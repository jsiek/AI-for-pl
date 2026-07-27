module
  proof.Quotient.NuImprecisionTargetInstantiationTransportExperiment
  where

-- File Charter:
--   * Tests whether exact target-instantiation creation recovers the
--     generalized renamed/store-embedded behavior needed by fusion clients.
--   * Proves the canonical transported result from the exact creation
--     constructor and the relation-wide closed-endpoint transport rule.
--   * Keeps arbitrary endpoint reindexing out of the experiment: the final
--     index is the canonical renaming of the exact creation index.
--   * Imports no legacy term-imprecision judgment and contains no postulate,
--     hole, permissive option, or termination bypass.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Imprecision using
  (ImpCtx; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴿᵢ)
open import ImprecisionComposition using (ImprecisionShape)
open import ImprecisionWf using
  (ImpAssm; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ; store-right)
open import NuTerms using
  (Term; Λ_; _⟨_⟩; renameᵗᵐ)
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using
  (Renameᵗ; Ty; TyCtx; ★; wf★; `∀; ⇑ᵗ; renameᵗ)
open import Relation.Binary.PropositionalEquality using (sym)
open import
  proof.Core.Properties.TypeProperties
  using (TyRenameWf)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using
  ( rename-assm²ᵢ
  ; ⊑-rename-at²ᵢ
  ; ⊑-renameᵗ²ᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  using
  ( rename-storeᴿ
  ; target-instantiationᴿ
  ; _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using (TargetInstantiationCreation)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)


target-instantiation-canonical-transportᴿ :
  ∀ {Φ₀ : ImpCtx} {Θᴸ Θᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
      (suc Θᴸ) (suc Θᴿ)}
    {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
    {W W′ : Term} {B C D : Ty} {s μ r f}
    {body-shape : ImprecisionShape}
    {Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Ψ Δᴸ Δᴿ}
    {τ σ : Renameᵗ} →
  TargetInstantiationCreation
    {Φ = Φ₀} {Δᴸ = Θᴸ} {Δᴿ = Θᴿ}
    {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ⁺}
    {W = W} {W′ = W′} {B = B} {C = C} {D = D}
    {s = s} {μ = μ} {r = r} {f = f}
    {body-shape = body-shape}
    (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
      ∣ suc Θᴸ ∣ suc Θᴿ ∣ ρ∀ ∣ []
      ⊢ᴿ W ⊑ W′ ⦂ D ⊑ C ∶ r) →
  (assm :
    ∀ {a : ImpAssm} → a ∈ ⇑ᴿᵢ Φ₀ →
      rename-assm²ᵢ τ σ a ∈ Ψ) →
  (hτ : TyRenameWf Θᴸ Δᴸ τ) →
  (hσ : TyRenameWf (suc Θᴿ) Δᴿ σ) →
  RelStoreEmbeddingⁱ τ σ
    (store-right zero ★ wf★ ∷ ρᴿ⁺) ρ →
  Δᴸ ∣ leftStoreⁱ ρ ∣ []
    ⊢ renameᵗᵐ τ (Λ W) ⦂ renameᵗ τ (`∀ D) →
  Δᴿ ∣ rightStoreⁱ ρ ∣ []
    ⊢ renameᵗᵐ σ (W′ ⟨ s ⟩) ⦂ renameᵗ σ (⇑ᵗ B) →
  Ψ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴿ renameᵗᵐ τ (Λ W) ⊑ renameᵗᵐ σ (W′ ⟨ s ⟩)
    ⦂ renameᵗ τ (`∀ D) ⊑ renameᵗ σ (⇑ᵗ B)
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ
        (⊑-target-lift-rightᵢ f)
target-instantiation-canonical-transportᴿ
    creation assm hτ hσ store-embedding
    source-typing target-typing =
  rename-storeᴿ assm hτ hσ store-embedding
    (target-instantiationᴿ creation)
    source-typing target-typing


target-instantiation-endpoint-transportᴿ :
  ∀ {Φ₀ : ImpCtx} {Θᴸ Θᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
      (suc Θᴸ) (suc Θᴿ)}
    {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
    {W W′ : Term} {B C D : Ty} {s μ r f}
    {body-shape : ImprecisionShape}
    {Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Ψ Δᴸ Δᴿ}
    {τ σ : Renameᵗ}
    {M M′ : Term} {A A′ : Ty}
    {p : Ψ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  TargetInstantiationCreation
    {Φ = Φ₀} {Δᴸ = Θᴸ} {Δᴿ = Θᴿ}
    {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ⁺}
    {W = W} {W′ = W′} {B = B} {C = C} {D = D}
    {s = s} {μ = μ} {r = r} {f = f}
    {body-shape = body-shape}
    (((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
      ∣ suc Θᴸ ∣ suc Θᴿ ∣ ρ∀ ∣ []
      ⊢ᴿ W ⊑ W′ ⦂ D ⊑ C ∶ r) →
  (assm :
    ∀ {a : ImpAssm} → a ∈ ⇑ᴿᵢ Φ₀ →
      rename-assm²ᵢ τ σ a ∈ Ψ) →
  (hτ : TyRenameWf Θᴸ Δᴸ τ) →
  (hσ : TyRenameWf (suc Θᴿ) Δᴿ σ) →
  RelStoreEmbeddingⁱ τ σ
    (store-right zero ★ wf★ ∷ ρᴿ⁺) ρ →
  renameᵗᵐ τ (Λ W) ≡ M →
  renameᵗᵐ σ (W′ ⟨ s ⟩) ≡ M′ →
  (source-type-eq : renameᵗ τ (`∀ D) ≡ A) →
  (target-type-eq : renameᵗ σ (⇑ᵗ B) ≡ A′) →
  ⊑-rename-at²ᵢ assm hτ hσ
    (sym source-type-eq) (sym target-type-eq)
    (⊑-target-lift-rightᵢ f) ≡ p →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ A′ →
  Ψ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
target-instantiation-endpoint-transportᴿ
    creation assm hτ hσ store-embedding
    refl refl refl refl refl source-typing target-typing =
  target-instantiation-canonical-transportᴿ
    creation assm hτ hσ store-embedding
    source-typing target-typing
