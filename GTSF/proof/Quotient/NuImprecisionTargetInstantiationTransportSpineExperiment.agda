module
  proof.Quotient.NuImprecisionTargetInstantiationTransportSpineExperiment
  where

-- File Charter:
--   * Tests finite nesting of exact target-instantiation creation followed by
--     endpoint renaming and relational-store embedding.
--   * Strengthens every transported step with equality between its final
--     imprecision index and the canonical transported creation index.
--   * Folds the strengthened spine into the independent smaller relation.
--   * Imports no legacy term-imprecision judgment and contains no postulate,
--     hole, permissive option, termination bypass, or catch-all clause.

open import Agda.Builtin.Equality using (_≡_)
open import CastImprecisionShape using (_⊢ᶜ_⦂_; widening)
open import Coercions using (Coercion; Inert; ModeEnv; inst)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (suc; zero)
open import Imprecision using
  (ImpCtx; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴿᵢ)
open import ImprecisionComposition using
  (ImprecisionShape; νˢ_; ⌊_⌋; _；_≋_)
open import ImprecisionWf using
  (ImpAssm; _∣_⊢_⊑_⊣_; ∀ⁱ_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-right
  )
open import NuTerms using
  (No•; Term; Value; Λ_; _⟨_⟩; renameᵗᵐ)
open import TermTyping using
  (CastMode; SealModeStore★; _∣_∣_⊢_⦂_)
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
  ; ⊑-target-lift-rightᵢ
  )
open import
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  using
  ( _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using
  ( StoreImpPrefixᴿ
  ; TargetInstantiationCreation
  ; target-instantiation-creation
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationTransportExperiment
  using (target-instantiation-endpoint-transportᴿ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef
  using (RelStoreEmbeddingⁱ)


data TargetInstantiationTransportSpine
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    (ρ : StoreImp Φ Δᴸ Δᴿ) :
    (M M′ : Term) → (A A′ : Ty) →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) → Set₁ where

  related-base :
    ∀ {M M′ A A′ p} →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
    TargetInstantiationTransportSpine ρ M M′ A A′ p

  creation-step :
    ∀ {Φ₀ : ImpCtx} {Θᴸ Θᴿ : TyCtx}
      {ρ₀ ρ⁺ : StoreImp Φ₀ Θᴸ Θᴿ}
      {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
        (suc Θᴸ) (suc Θᴿ)}
      {ρᴿ⁺ : StoreImp (⇑ᴿᵢ Φ₀) Θᴸ (suc Θᴿ)}
      {τ σ : Renameᵗ}
      {W W′ M M′ : Term}
      {A A′ B C D : Ty}
      {s : Coercion} {μ : ModeEnv}
      {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀)
        ∣ suc Θᴸ ⊢ D ⊑ C ⊣ suc Θᴿ}
      {f : Φ₀ ∣ Θᴸ ⊢ `∀ D ⊑ B ⊣ Θᴿ}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {body-shape : ImprecisionShape} →
    StoreImpPrefixᴿ ρ₀ ρ⁺ →
    CastMode μ →
    SealModeStore★ μ (rightStoreⁱ ρ₀) →
    μ ∣ Θᴿ ∣ rightStoreⁱ ρ₀
      ⊢ inst B s ∶ `∀ C ⊑ B →
    LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ₀) ρ₀ ρ∀ →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ₀) ρ⁺ ρᴿ⁺ →
    Value W →
    No• W →
    Value W′ →
    No• W′ →
    Inert s →
    TargetInstantiationTransportSpine ρ∀ W W′ D C r →
    widening ⊢ᶜ inst B s ⦂ νˢ body-shape →
    ⌊ ∀ⁱ r ⌋ ； νˢ body-shape ≋ ⌊ f ⌋ →
    Θᴸ
      ∣ leftStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
      ∣ [] ⊢ Λ W ⦂ `∀ D →
    suc Θᴿ
      ∣ rightStoreⁱ (store-right zero ★ wf★ ∷ ρᴿ⁺)
      ∣ [] ⊢ W′ ⟨ s ⟩ ⦂ ⇑ᵗ B →
    (assm :
      ∀ {a : ImpAssm} → a ∈ ⇑ᴿᵢ Φ₀ →
        rename-assm²ᵢ τ σ a ∈ Φ) →
    (hτ : TyRenameWf Θᴸ Δᴸ τ) →
    (hσ : TyRenameWf (suc Θᴿ) Δᴿ σ) →
    RelStoreEmbeddingⁱ τ σ
      (store-right zero ★ wf★ ∷ ρᴿ⁺) ρ →
    (source-eq : renameᵗᵐ τ (Λ W) ≡ M) →
    (target-eq : renameᵗᵐ σ (W′ ⟨ s ⟩) ≡ M′) →
    (source-type-eq : renameᵗ τ (`∀ D) ≡ A) →
    (target-type-eq : renameᵗ σ (⇑ᵗ B) ≡ A′) →
    ⊑-rename-at²ᵢ assm hτ hσ
      (sym source-type-eq) (sym target-type-eq)
      (⊑-target-lift-rightᵢ f) ≡ p →
    Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A →
    Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ A′ →
    TargetInstantiationTransportSpine ρ M M′ A A′ p


target-instantiation-transport-spine-foldᴿ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A A′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  TargetInstantiationTransportSpine ρ M M′ A A′ p →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p
target-instantiation-transport-spine-foldᴿ (related-base relation) =
  relation
target-instantiation-transport-spine-foldᴿ
    (creation-step
      prefix mode seal-mode inst-typing matched-store-lift
      right-store-lift source-value source-no-bullet
      target-value target-no-bullet inert tail
      inst-shape index-composition
      canonical-source-typing canonical-target-typing
      assm hτ hσ store-embedding
      source-eq target-eq source-type-eq target-type-eq
      index-eq source-typing target-typing) =
  target-instantiation-endpoint-transportᴿ
    (target-instantiation-creation
      prefix mode seal-mode inst-typing matched-store-lift
      right-store-lift source-value source-no-bullet
      target-value target-no-bullet inert
      (target-instantiation-transport-spine-foldᴿ tail)
      inst-shape index-composition
      canonical-source-typing canonical-target-typing)
    assm hτ hσ store-embedding
    source-eq target-eq source-type-eq target-type-eq
    index-eq source-typing target-typing
