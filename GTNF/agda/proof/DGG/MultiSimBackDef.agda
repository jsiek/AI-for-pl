module proof.DGG.MultiSimBackDef where

-- File Charter:
--   * THE STATEMENT of the backward simulation over a run `r′` of the less precise
--     side: the right continues by `r″` past where `r′` ends.
--   * STATEMENT ONLY (Def/Proof/Lemma, PLAN.md §1): the proof is
--     MultiSimBackProof.agda, parameterized at the module level.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_)
open import Data.Sum using (_⊎_)

open import Types using (Ty)
open import Ctx using (Ctxᵗ; WfCtx; Alloc; apply)
open import Coercion using (Label)
open import Terms using (Term; Value; blame; _∣_⊢_⦂_)
open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; _then_; runCtx)
open import ImprecisionWorld
  using (World; WfWorld; _⊑ᵂ⟨_⟩_; CtxImp; lhs; rhs)
open import TermImprecision using (_∣_⊢_⊑_∶_)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; applyˢ; allocs; _++ʳ_; ↑ᴹ*[_])

SimBack* : Set
SimBack* = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M M′ N′ : Term} {A A′ : Ty}
             {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → (r′ : Δ′ ⊢ M′ -→* N′)
  → (∃[ N₂ ] ∃[ N₂′ ] Σ[ r ∈ Δ ⊢ M -→* N₂ ]
       Σ[ r″ ∈ runCtx r′ ⊢ N′ -→* N₂′ ]
       Σ[ W′ ∈ World (applyˢ (allocs r) Δ)
                     (applyˢ (allocs (r′ ++ʳ r″)) Δ′) ]
         (W ⟿[ allocs r ∣ allocs (r′ ++ʳ r″) ] W′) × WfWorld W′
         × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N₂ ⊑ N₂′ ∶ q))
    ⊎ (∃[ ℓ ] (Δ ⊢ M -→* blame ℓ))
