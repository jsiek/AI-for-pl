module proof.DGG.CatchupBlameDef where

-- File Charter:
--   * THE STATEMENT of `M ⊑ blame ℓ`: the more precise side reaches blame too (only
--     one-sided left wrappers over `blame⊑` relate anything to blame).
--   * STATEMENT ONLY (Def/Proof/Lemma, PLAN.md §1): the proof is
--     CatchupBlameProof.agda, parameterized at the module level.
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
  using (World; ⌈_⌉; WfWorld; _⊑ᵂ⟨_⟩_; CtxImp; lhs; rhs)
open import TermImprecision using (_∣_⊢_⊑_∶_)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; applyˢ; allocs; _++ʳ_; ↑ᴹ*[_])

CatchupBlame : Set
CatchupBlame = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M : Term} {ℓ : Label}
                 {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → ⌈ W ⌉ ∣ [] ⊢ M ⊑ blame ℓ ∶ p
  → ∃[ ℓ′ ] (Δ ⊢ M -→* blame ℓ′)
