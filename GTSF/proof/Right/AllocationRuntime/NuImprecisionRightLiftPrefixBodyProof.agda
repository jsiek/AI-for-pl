module
  proof.Right.AllocationRuntime.NuImprecisionRightLiftPrefixBodyProof
  where

-- File Charter:
--   * Proves the canonical strict `RightLiftPrefixBodyᵀ` contract.
--   * Reconstructs the target-right lift proof from low-level world-embedding
--     support without importing the broad simulation module.
--   * Uses the canonical relational-store lift embedding and the focused
--     no-runtime-bullet traversal.
--   * Contains only total proof terms, with no permissive option or dispatcher.

open import proof.NuCore.Relations.NuImprecisionQuotientedTyping
open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Nat.Properties using (≤-refl)
open import ImprecisionWf using (⇑ᴿᵢ)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftRightStoreⁱ
  ; StoreImp
  )
open import NuTerms using (renameᵗᵐ; ⇑ᵗᵐ)
open import QuotientedTermImprecision using (allocation-prefixᵀ)
open import Types using (renameᵗ)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( RelWorldEmbeddingⁱ
  ; castModeRenamer-id
  ; rel-world-embedding
  )
open import
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  using
  ( nu-term-imprecision-transport-termsᵀ
  ; nu-term-imprecision-transport-typesᵀ
  )
open import proof.Core.Properties.NuTermProperties using
  ( renameᵗᵐ-id
  ; renameᵗᵐ-preserves-No•
  )
open import proof.Core.Properties.TypePreservation using
  (castModeRenamer-suc; term-weaken)
open import proof.Core.Properties.TypeProperties using
  ( RenameLeftInverse-suc
  ; TyRenameWf-suc
  ; predᵗ
  ; renameᵗ-id
  )
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  ( rename-assm²-target-rightᵢ
  ; ⊑-target-lift-rightᵢ
  )
open import proof.NuCore.Misc.NuImprecisionWorldEmbeddingNoBullet using
  (rel-world-embed-no•ᵀ)
open import proof.Right.AllocationRuntime.NuImprecisionRightLiftPrefixBodyDef
  using (RightLiftPrefixBodyᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)
open import proof.Store.RelEmbedding.NuImprecisionRelCtxRenameDef using
  (rel-ctx-rename-[])
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (lift-right-store-embeddingⁱ)


private
  right-lift-world-embeddingⁱ :
    ∀ {Φ Δᴸ Δᴿ}
      {ρ : StoreImp Φ Δᴸ Δᴿ}
      {ρ′ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)} →
    LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρ′ →
    RelWorldEmbeddingⁱ (λ X → X) suc (λ X → X) predᵗ
      rename-assm²-target-rightᵢ (λ X<Δ → X<Δ) TyRenameWf-suc
      {ρ = ρ} {ρ′ = ρ′} {γ = []} {γ′ = []}
  right-lift-world-embeddingⁱ liftρ =
    rel-world-embedding (λ X → refl) RenameLeftInverse-suc
      castModeRenamer-id castModeRenamer-suc
      (lift-right-store-embeddingⁱ liftρ) rel-ctx-rename-[]


right-lift-prefix-body-proofᵀ : RightLiftPrefixBodyᵀ
right-lift-prefix-body-proofᵀ {A = A} {L = L}
    liftρ prefix noL noL′ L⊑L′ =
  allocation-prefixᵀ prefix body
    (term-weaken ≤-refl (leftStoreⁱ-prefix-inclusion prefix)
      noL (nu-term-imprecision-source-typing body))
    (term-weaken ≤-refl (rightStoreⁱ-prefix-inclusion prefix)
      noL′↑ (nu-term-imprecision-target-typing body))
  where
  body =
    nu-term-imprecision-transport-termsᵀ (renameᵗᵐ-id L) refl
      (nu-term-imprecision-transport-typesᵀ
        (renameᵗ-id A) refl refl
        (rel-world-embed-no•ᵀ
          (right-lift-world-embeddingⁱ liftρ) L⊑L′ noL noL′))
  noL′↑ = renameᵗᵐ-preserves-No• suc noL′
