module proof.DGG.CatchupRightDef where

-- File Charter:
--   * THE STATEMENT of a left VALUE: the less precise side finishes its administrative
--     steps (casts, Inst/TyBeta, Merge, IdDyn, Id) and reaches a related
--     value.
--   * STATEMENT ONLY (Def/Proof/Lemma, PLAN.md §1): the proof is
--     CatchupRightProof.agda, parameterized at the module level.
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

CatchupRight : Set
CatchupRight = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V M′ : Term} {A A′ : Ty}
                 {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W
  → Value V
  → W ∣ [] ⊢ V ⊑ M′ ∶ p
  → ∃[ V′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* V′ ] Value V′
      × Σ[ W′ ∈ World Δ (applyˢ (allocs r′) Δ′) ]
        (W ⟿[ [] ∣ allocs r′ ] W′) × WfWorld W′
        × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ V ⊑ V′ ∶ q)
