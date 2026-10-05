module proof.DGG.MultiSimDef where

-- File Charter:
--   * THE STATEMENT of the forward simulation over a run of the more precise side.
--   * STATEMENT ONLY (Def/Proof/Lemma, PLAN.md §1): the proof is
--     MultiSimProof.agda, parameterized at the module level.
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
  using (World; πʷ; WfWorld; _⊑ᵂ⟨_⟩_; CtxImp; lhs; rhs)
open import TermImprecision using (_∣_⊢_⊑_∶_)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; applyˢ; allocs; _++ʳ_; ↑ᴹ*[_])

Sim* : Set
Sim* = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M M′ N : Term} {A A′ : Ty}
         {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W → πʷ W ≡ []
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → (r : Δ ⊢ M -→* N)
  → ∃[ N′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* N′ ]
      Σ[ W′ ∈ World (applyˢ (allocs r) Δ) (applyˢ (allocs r′) Δ′) ]
        (W ⟿[ allocs r ∣ allocs r′ ] W′) × WfWorld W′
        × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N ⊑ N′ ∶ q)
