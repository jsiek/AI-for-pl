module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextProof
  where

-- File Charter:
--   * Constructs the exact post-allocation paired-lambda target-instantiation
--     relation with `Λ⊑instβᵀ`.
--   * Supplies the canonical closed endpoints, final values, and final
--     no-bullet evidence while preserving the retained store, cast,
--     body relation, arbitrary universal root, and endpoint-typing
--     provenance.
--   * Contains no catch-up implementation, recursive dispatcher,
--     result/view/outcome type, postulate, hole, permissive option,
--     termination bypass, or broad DGG import.

open import Imprecision using (_ˣ⊑★; _ˣ⊑ˣ_)
open import NuTerms using
  ( no•-Λ
  ; no•-⟨⟩
  ; Λ_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using (Λ⊑instβᵀ)
open import TermTyping using (forget)
open import Types using (`∀; ⇑ᵗ)
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-id; typing-closedᵐ)
open import proof.Core.Properties.TypeProperties using
  (renameᵗ-id)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using (⊑-target-lift-rightᵢ)
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextDef
  using
  (WorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextᵀ)


world-coherent-right-target-widen-instantiation-paired-lambda-post-beta-context-proofᵀ :
  WorldCoherentRightTargetWidenInstantiationPairedLambdaPostBetaContextᵀ
world-coherent-right-target-widen-instantiation-paired-lambda-post-beta-context-proofᵀ
    {W = W} {W′ = W′} {B = B} {D = D} {s = s}
    {f = f}
    prefix mode seal★ inst⊑ liftρ liftρᴿ
    vW noW vW′ noW′ inert body source-typing target-typing =
  Λ⊑instβᵀ
    {τ = λ X → X} {σ = λ X → X}
    {M = Λ W} {M′ = W′ ⟨ s ⟩}
    {A = `∀ D} {A′ = ⇑ᵗ B}
    prefix mode seal★ inst⊑ liftρ liftρᴿ
    vW noW vW′ noW′ inert body f
    (λ { {a = X ˣ⊑★} a∈ → a∈
       ; {a = X ˣ⊑ˣ Y} a∈ → a∈ })
    (λ X<Δᴸ → X<Δᴸ)
    (λ X<Δᴿ → X<Δᴿ)
    rel-store-embedding-reflⁱ
    (renameᵗᵐ-id (Λ W))
    (renameᵗᵐ-id (W′ ⟨ s ⟩))
    (renameᵗ-id (`∀ D))
    (renameᵗ-id (⇑ᵗ B))
    (⊑-target-lift-rightᵢ f)
    (Λ vW)
    (no•-Λ noW)
    (typing-closedᵐ (forget source-typing))
    (vW′ ⟨ inert ⟩)
    (no•-⟨⟩ noW′)
    (typing-closedᵐ (forget target-typing))
    source-typing target-typing
