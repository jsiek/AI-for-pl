module proof.DGG.EvolveImpDef where

-- File Charter:
--   * THE STATEMENT of transport of `⊑` along world evolution (PLAN.md §3; approved by
--     Jeremy, 2026-10-02): the two terms are shifted by their sides'
--     allocations, as the congruence rules shift siblings.
--   * STATEMENT ONLY (Def/Proof/Lemma, PLAN.md §1): the proof is
--     EvolveImpProof.agda, parameterized at the module level.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty)
open import Ctx using (Ctxᵗ; WfCtx; Alloc; apply)
open import Coercion using (Label)
open import Terms using (Term; Value; blame; _∣_⊢_⦂_)
open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; _then_; runCtx)
open import ImprecisionWorld
  using (World; πʷ; κʷ; WfWorld; _⊑ᵂ⟨_⟩_; CtxImp; lhs; rhs)
open import TermImprecision using (_∣_⊢_⊑_∶_)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; applyˢ; allocs; _++ʳ_; ↑ᴹ*[_])

EvolveImp : Set
EvolveImp = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {ξs ξs′ : List Alloc}
              {W′ : World (applyˢ ξs Δ) (applyˢ ξs′ Δ′)}
              {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WfCtx Δ → WfCtx Δ′
  → W ⟿[ ξs ∣ ξs′ ] W′
  → WfWorld W → πʷ W ≡ [] → κʷ W ≡ []
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld W′
    × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ ↑ᴹ*[ ξs ] M ⊑ ↑ᴹ*[ ξs′ ] M′ ∶ q)
