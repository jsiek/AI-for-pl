module
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  where

-- File Charter:
--   * Projects endpoint typing, value, and no-bullet evidence from the
--     composable embedded target-instantiation creation residual.
--   * Proves each property by structural recursion over exact creation and
--     composed world embeddings.
--   * Imports no term-imprecision judgment and contains no postulate, hole,
--     permissive option, termination bypass, or catch-all clause.

open import Data.List using ([])

open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  ( No•
  ; Term
  ; Value
  ; Λ_
  ; _⟨_⟩
  ; no•-Λ
  ; no•-⟨⟩
  )
open import TermTyping using (_∣_∣_⊢_⦂_)
open import Types using (Ty)
open import proof.Core.Properties.NuTermProperties using
  ( renameᵗᵐ-preserves-No•
  ; renameᵗᵐ-preserves-Value
  )
open import
  proof.Quotient.NuImprecisionTargetInstantiationCreationDef
  using
  ( EmbeddedTargetInstantiationCreation
  ; TargetInstantiationCreation
  ; embed-creationᴱ
  ; exact-creationᴱ
  )


embedded-creation-source-typingᴱ :
  ∀ {Φ₀ Θᴸ Θᴿ ρ₀ ρ⁺ ρ∀ ρᴿ W W′ B C D s μ r f
      body-shape body-relation Ψ Δᴸ Δᴿ ρ M M′ A A′ p} →
  EmbeddedTargetInstantiationCreation
    {Φ₀ = Φ₀} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
    {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
    {W = W} {W′ = W′} {B = B} {C = C} {D = D}
    {s = s} {μ = μ} {r = r} {f = f}
    {body-shape = body-shape}
    body-relation
    {Ψ = Ψ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ρ M M′ A A′ p →
  Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ A
embedded-creation-source-typingᴱ (exact-creationᴱ creation) =
  TargetInstantiationCreation.source-result-typing creation
embedded-creation-source-typingᴱ
    (embed-creationᴱ embedded assm hτ hσ store-embedding
      source-typing target-typing) =
  source-typing


embedded-creation-target-typingᴱ :
  ∀ {Φ₀ Θᴸ Θᴿ ρ₀ ρ⁺ ρ∀ ρᴿ W W′ B C D s μ r f
      body-shape body-relation Ψ Δᴸ Δᴿ ρ M M′ A A′ p} →
  EmbeddedTargetInstantiationCreation
    {Φ₀ = Φ₀} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
    {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
    {W = W} {W′ = W′} {B = B} {C = C} {D = D}
    {s = s} {μ = μ} {r = r} {f = f}
    {body-shape = body-shape}
    body-relation
    {Ψ = Ψ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ρ M M′ A A′ p →
  Δᴿ ∣ rightStoreⁱ ρ ∣ [] ⊢ M′ ⦂ A′
embedded-creation-target-typingᴱ (exact-creationᴱ creation) =
  TargetInstantiationCreation.target-result-typing creation
embedded-creation-target-typingᴱ
    (embed-creationᴱ embedded assm hτ hσ store-embedding
      source-typing target-typing) =
  target-typing


embedded-creation-source-valueᴱ :
  ∀ {Φ₀ Θᴸ Θᴿ ρ₀ ρ⁺ ρ∀ ρᴿ W W′ B C D s μ r f
      body-shape body-relation Ψ Δᴸ Δᴿ ρ M M′ A A′ p} →
  EmbeddedTargetInstantiationCreation
    {Φ₀ = Φ₀} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
    {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
    {W = W} {W′ = W′} {B = B} {C = C} {D = D}
    {s = s} {μ = μ} {r = r} {f = f}
    {body-shape = body-shape}
    body-relation
    {Ψ = Ψ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ρ M M′ A A′ p →
  Value M
embedded-creation-source-valueᴱ (exact-creationᴱ creation) =
  Λ (TargetInstantiationCreation.source-body-value creation)
embedded-creation-source-valueᴱ
    (embed-creationᴱ embedded assm hτ hσ store-embedding
      source-typing target-typing) =
  renameᵗᵐ-preserves-Value _
    (embedded-creation-source-valueᴱ embedded)


embedded-creation-target-valueᴱ :
  ∀ {Φ₀ Θᴸ Θᴿ ρ₀ ρ⁺ ρ∀ ρᴿ W W′ B C D s μ r f
      body-shape body-relation Ψ Δᴸ Δᴿ ρ M M′ A A′ p} →
  EmbeddedTargetInstantiationCreation
    {Φ₀ = Φ₀} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
    {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
    {W = W} {W′ = W′} {B = B} {C = C} {D = D}
    {s = s} {μ = μ} {r = r} {f = f}
    {body-shape = body-shape}
    body-relation
    {Ψ = Ψ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ρ M M′ A A′ p →
  Value M′
embedded-creation-target-valueᴱ (exact-creationᴱ creation) =
  TargetInstantiationCreation.target-body-value creation
    ⟨ TargetInstantiationCreation.body-cast-inert creation ⟩
embedded-creation-target-valueᴱ
    (embed-creationᴱ embedded assm hτ hσ store-embedding
      source-typing target-typing) =
  renameᵗᵐ-preserves-Value _
    (embedded-creation-target-valueᴱ embedded)


embedded-creation-source-no-bulletᴱ :
  ∀ {Φ₀ Θᴸ Θᴿ ρ₀ ρ⁺ ρ∀ ρᴿ W W′ B C D s μ r f
      body-shape body-relation Ψ Δᴸ Δᴿ ρ M M′ A A′ p} →
  EmbeddedTargetInstantiationCreation
    {Φ₀ = Φ₀} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
    {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
    {W = W} {W′ = W′} {B = B} {C = C} {D = D}
    {s = s} {μ = μ} {r = r} {f = f}
    {body-shape = body-shape}
    body-relation
    {Ψ = Ψ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ρ M M′ A A′ p →
  No• M
embedded-creation-source-no-bulletᴱ (exact-creationᴱ creation) =
  no•-Λ (TargetInstantiationCreation.source-body-no-bullet creation)
embedded-creation-source-no-bulletᴱ
    (embed-creationᴱ embedded assm hτ hσ store-embedding
      source-typing target-typing) =
  renameᵗᵐ-preserves-No• _
    (embedded-creation-source-no-bulletᴱ embedded)


embedded-creation-target-no-bulletᴱ :
  ∀ {Φ₀ Θᴸ Θᴿ ρ₀ ρ⁺ ρ∀ ρᴿ W W′ B C D s μ r f
      body-shape body-relation Ψ Δᴸ Δᴿ ρ M M′ A A′ p} →
  EmbeddedTargetInstantiationCreation
    {Φ₀ = Φ₀} {Θᴸ = Θᴸ} {Θᴿ = Θᴿ}
    {ρ₀ = ρ₀} {ρ⁺ = ρ⁺} {ρ∀ = ρ∀} {ρᴿ⁺ = ρᴿ}
    {W = W} {W′ = W′} {B = B} {C = C} {D = D}
    {s = s} {μ = μ} {r = r} {f = f}
    {body-shape = body-shape}
    body-relation
    {Ψ = Ψ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    ρ M M′ A A′ p →
  No• M′
embedded-creation-target-no-bulletᴱ (exact-creationᴱ creation) =
  no•-⟨⟩ (TargetInstantiationCreation.target-body-no-bullet creation)
embedded-creation-target-no-bulletᴱ
    (embed-creationᴱ embedded assm hτ hσ store-embedding
      source-typing target-typing) =
  renameᵗᵐ-preserves-No• _
    (embedded-creation-target-no-bulletᴱ embedded)
