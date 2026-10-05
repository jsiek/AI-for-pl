module proof.DGG.CatchupLeftDef where

-- File Charter:
--   * THE STATEMENT of a right VALUE: the more precise side reaches a related value, or
--     blame (a pending check on the more precise side may fail).
--   * STATEMENT ONLY (Def/Proof/Lemma, PLAN.md §1): the proof is
--     CatchupLeftProof.agda, parameterized at the module level.
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

CatchupLeft : Set
CatchupLeft = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M V′ : Term} {A A′ : Ty}
                {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W → πʷ W ≡ []
  → Value V′
  → W ∣ [] ⊢ M ⊑ V′ ∶ p
  → (∃[ V ] Σ[ r ∈ Δ ⊢ M -→* V ] Value V
       × Σ[ W′ ∈ World (applyˢ (allocs r) Δ) Δ′ ]
         (W ⟿[ allocs r ∣ [] ] W′) × WfWorld W′
         × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ V ⊑ V′ ∶ q))
    ⊎ (∃[ ℓ ] (Δ ⊢ M -→* blame ℓ))
