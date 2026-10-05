module proof.DGG.SimBackDef where

-- File Charter:
--   * THE STATEMENT of the BACKWARD simulation step (PLAN.md §3; approved by Jeremy,
--     2026-10-02).  The less precise (right) side takes one step `st′`;
--     then both sides take zero or more steps (the right's continuation
--     is `r″`, so its whole run is `st′ then r″`) into a related pair,
--     or the more precise side reaches blame.  `WfCtx` premises as in
--     Sim.
--   * STATEMENT ONLY (Def/Proof/Lemma, PLAN.md §1): the proof is
--     SimBackProof.agda, parameterized at the module level.
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

SimBack : Set
SimBack = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M M′ N′ : Term} {A A′ : Ty}
            {p : A ⊑ᵂ⟨ W ⟩ A′} {ξ′ : Alloc}
  → WfCtx Δ → WfCtx Δ′ → WfWorld W → πʷ W ≡ []
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → (st′ : Δ′ ⊢ M′ -→ N′ ∣ ξ′)
  → (∃[ N₂ ] ∃[ N₂′ ] Σ[ r ∈ Δ ⊢ M -→* N₂ ]
       Σ[ r″ ∈ apply ξ′ Δ′ ⊢ N′ -→* N₂′ ]
       Σ[ W′ ∈ World (applyˢ (allocs r) Δ)
                     (applyˢ (allocs (st′ then r″)) Δ′) ]
         (W ⟿[ allocs r ∣ allocs (st′ then r″) ] W′) × WfWorld W′
         × Σ[ q ∈ A ⊑ᵂ⟨ W′ ⟩ A′ ] (W′ ∣ [] ⊢ N₂ ⊑ N₂′ ∶ q))
    ⊎ (∃[ ℓ ] (Δ ⊢ M -→* blame ℓ))
