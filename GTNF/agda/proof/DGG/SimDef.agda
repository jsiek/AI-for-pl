module proof.DGG.SimDef where

-- File Charter:
--   * THE STATEMENT of the FORWARD simulation step (PLAN.md §3; approved by Jeremy,
--     2026-10-02).  The more precise (left) side takes one step; the
--     less precise (right) side takes zero or more steps; the new world
--     evolves from the old one along both sides' allocations.  The
--     `WfCtx` premises are an addition to the approved statement
--     (pre-authorized: every caller supplies them; Preservation needs
--     them).
--   * STATEMENT ONLY (Def/Proof/Lemma, PLAN.md §1): the proof is
--     SimProof.agda, parameterized at the module level.
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

Sim : Set
Sim = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M M′ N : Term} {A A′ : Ty}
        {p : A ⊑ᵂ⟨ W ⟩ A′} {ξ : Alloc}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → Δ ⊢ M -→ N ∣ ξ
  → ∃[ N′ ] Σ[ r′ ∈ Δ′ ⊢ M′ -→* N′ ]
      Σ[ W′ ∈ World (apply ξ Δ) (applyˢ (allocs r′) Δ′) ]
        (W ⟿[ ξ ∷ [] ∣ allocs r′ ] W′) × WfWorld W′
        × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N ⊑ N′ ∶ q)
