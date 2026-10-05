module proof.DGG.ImprecisionTypingDef where

-- File Charter:
--   * THE STATEMENT of a `⊑` derivation gives both typings (the relation carries the
--     side premises for this, TermImprecision's charter), at any world,
--     with or without pending names (design.md D27): the index opens
--     the left type, but the typing is at the ACTUAL left type A.
--   * STATEMENT ONLY (Def/Proof/Lemma, PLAN.md §1): the proof is
--     ImprecisionTypingProof.agda, parameterized at the module level.
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
  using (World; _⊑ᵂ⟨_⟩_; CtxImp; lhs; rhs)
open import TermImprecision using (_∣_⊢_⊑_∶_)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; applyˢ; allocs; _++ʳ_; ↑ᴹ*[_])

ImprecisionTyping : Set
ImprecisionTyping = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {γ : CtxImp W}
                      {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
  → (Δ ∣ lhs γ ⊢ M ⦂ A) × (Δ′ ∣ rhs γ ⊢ M′ ⦂ A′)
