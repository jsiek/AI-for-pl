open import TypeSafety using (Preservation; PreservationWf; Determinism)
open import proof.DGG.SimBackDef using (SimBack)
open import proof.DGG.ImprecisionTypingDef using (ImprecisionTyping)

module proof.DGG.MultiSimBackProof
  (simBack : SimBack)
  (impTyping : ImprecisionTyping)
  (preservation : Preservation)
  (preservationWf : PreservationWf)
  (determinism : Determinism)
  where

-- File Charter:
--   * THE PROOF OF `SimBack*` (MultiSimBackDef.agda) from `SimBack`, by
--     induction on the right run (GTLC's `sim-back*`, flipped).
--     Parameterized at the module level (proof/DGG/PLAN.md §1).
--   * One right step `st′` is simulated by `SimBack`, which may run the
--     right further, by `r₁″`, than the given run `r′₀` after `st′`.
--     By determinism (`prefix`), one of `r₁″` and `r′₀` extends the
--     other (equal allocations, which is all the statements see):
--     - `r′₀` is the shorter: SimBack's pair is the answer, the right
--       continuing past `r′₀` by the rest of `r₁″`;
--     - `r₁″` is the shorter: recurse on the rest of `r′₀` from
--       SimBack's pair.  The rest is a suffix, not a subterm, of the
--       run, so the recursion is on a bound on the run's length (`go`).
--   * Runs are concatenated by `_++ʳ′_`, evolutions composed by
--     `evolved-trans`, and the allocation lists re-associated
--     (proof/DGG/EvolveLemmas).

open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; _+_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤n+m)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Types using (Ty)
open import Ctx using (Ctxᵗ; WfCtx; apply)
open import Coercion using (Label)
open import Terms using (Term; blame; _∣_⊢_⦂_)
open import Reduction using (_⊢_-→*_; done; _then_; runCtx)
open import ImprecisionWorld using (World; WfWorld; _⊑ᵂ⟨_⟩_)
open import TermImprecision using (_∣_⊢_⊑_∶_)
open import proof.DGG.MultiSimBackDef using (SimBack*)
open import proof.DGG.Evolve
  using (_⟿[_∣_]_; ev-done; applyˢ; allocs; runCtx≡applyˢ; _++ʳ_)
open import proof.DGG.EvolveLemmas
  using (Evolved; len; len-++ʳ; allocs-++ʳ; runCtx-++ʳ; castʳ;
         allocs-castʳ; runCtx-castʳ; _++ʳ′_; allocs-++ʳ′;
         evolved-trans; evolved-cast)
open import proof.DGG.RunTyping preservation preservationWf using (wfˢ)

private
  variable
    Γ : Ctxᵗ
    L N₁ N₂ : Term
    A : Ty

------------------------------------------------------------------------
-- Two runs from one typed term: one extends the other
------------------------------------------------------------------------

prefix : WfCtx Γ → Γ ∣ [] ⊢ L ⦂ A
  → (r₁ : Γ ⊢ L -→* N₁) (r₂ : Γ ⊢ L -→* N₂)
  → (Σ[ s ∈ runCtx r₁ ⊢ N₁ -→* N₂ ] (allocs (r₁ ++ʳ s) ≡ allocs r₂))
    ⊎ (Σ[ s ∈ runCtx r₂ ⊢ N₂ -→* N₁ ] (allocs (r₂ ++ʳ s) ≡ allocs r₁))
prefix wf ⊢L done r₂ = inj₁ (r₂ , refl)
prefix wf ⊢L (st₁ then r₁) done = inj₂ ((st₁ then r₁) , refl)
prefix wf ⊢L (st₁ then r₁) (st₂ then r₂) with determinism ⊢L st₁ st₂
prefix wf ⊢L (st₁ then r₁) (st₂ then r₂) | refl , refl
    with prefix (preservationWf wf ⊢L st₁) (preservation wf ⊢L st₁) r₁ r₂
prefix wf ⊢L (st₁ then r₁) (st₂ then r₂) | refl , refl | inj₁ (s , eq) =
  inj₁ (s , cong (_ ∷_) eq)
prefix wf ⊢L (st₁ then r₁) (st₂ then r₂) | refl , refl | inj₂ (s , eq) =
  inj₂ (s , cong (_ ∷_) eq)

------------------------------------------------------------------------
-- SimBack*, by recursion on a bound of the right run's length
------------------------------------------------------------------------

private
  -- the rest of a run after a prefix is no longer than the run
  len-rest : ∀ {Γ L M N} {n : ℕ} (r₁ : Γ ⊢ L -→* M)
    (s : runCtx r₁ ⊢ M -→* N) (r : Γ ⊢ L -→* N)
    → allocs (r₁ ++ʳ s) ≡ allocs r → len r ≤ n → len s ≤ n
  len-rest r₁ s r eq le =
    ≤-trans (subst (len s ≤_)
                   (trans (sym (len-++ʳ r₁ s)) (cong length eq))
                   (m≤n+m (len s) (len r₁)))
            le

  go : ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {M M′ N′ : Term} {A A′ : Ty}
         {p : A ⊑ᵂ⟨ W ⟩ A′} (n : ℕ)
    → WfCtx Δ → WfCtx Δ′ → WfWorld W
    → W ∣ [] ⊢ M ⊑ M′ ∶ p
    → (r′ : Δ′ ⊢ M′ -→* N′)
    → len r′ ≤ n
    → (Σ[ N₂ ∈ Term ] Σ[ N₂′ ∈ Term ] Σ[ r ∈ Δ ⊢ M -→* N₂ ]
         Σ[ r″ ∈ runCtx r′ ⊢ N′ -→* N₂′ ]
           Evolved W (allocs r) (allocs (r′ ++ʳ r″)) A A′ N₂ N₂′)
      ⊎ (Σ[ ℓ ∈ Label ] (Δ ⊢ M -→* blame ℓ))
  go {W = W} {M = M} {M′ = M′} n wfΔ wfΔ′ wfW M⊑M′ done le =
    inj₁ (M , M′ , done , done , W , ev-done , wfW , _ , M⊑M′)
  go zero wfΔ wfΔ′ wfW M⊑M′ (st′ then r′₀) ()
  go (suc n) wfΔ wfΔ′ wfW M⊑M′ (st′ then r′₀) (s≤s le)
      with simBack wfΔ wfΔ′ wfW M⊑M′ st′
  go (suc n) wfΔ wfΔ′ wfW M⊑M′ (st′ then r′₀) (s≤s le)
    | inj₂ M↠blame = inj₂ M↠blame
  go (suc n) wfΔ wfΔ′ wfW M⊑M′ (st′ then r′₀) (s≤s le)
    | inj₁ (N₂ , N₂′ , r₁ , r₁″ , W₁ , ev₁ , wfW₁ , q₁ , N₂⊑N₂′)
      with prefix (preservationWf wfΔ′ (proj₂ (impTyping M⊑M′)) st′)
                  (preservation wfΔ′ (proj₂ (impTyping M⊑M′)) st′) r₁″ r′₀
  -- r′₀ is a prefix of r₁″: SimBack's pair is the answer
  go (suc n) wfΔ wfΔ′ wfW M⊑M′ (st′ then r′₀) (s≤s le)
    | inj₁ (N₂ , N₂′ , r₁ , r₁″ , W₁ , ev₁ , wfW₁ , q₁ , N₂⊑N₂′)
    | inj₂ (s , eq) =
    inj₁ (N₂ , N₂′ , r₁ , s
         , evolved-cast refl (cong (_ ∷_) (sym eq))
             (W₁ , ev₁ , wfW₁ , q₁ , N₂⊑N₂′))
  -- r₁″ is a prefix of r′₀: recurse on the rest s of r′₀
  go {Δ′ = Δ′} (suc n) wfΔ wfΔ′ wfW M⊑M′ (st′ then r′₀) (s≤s le)
    | inj₁ (N₂ , N₂′ , r₁ , r₁″ , W₁ , ev₁ , wfW₁ , q₁ , N₂⊑N₂′)
    | inj₁ (s , eq)
      with go n (wfˢ wfΔ (proj₁ (impTyping M⊑M′)) r₁)
                (wfˢ wfΔ′ (proj₂ (impTyping M⊑M′)) (st′ then r₁″))
                wfW₁ N₂⊑N₂′ (castʳ (runCtx≡applyˢ r₁″) s)
                (subst (_≤ n)
                       (sym (cong length
                              (allocs-castʳ (runCtx≡applyˢ r₁″) s)))
                       (len-rest r₁″ s r′₀ eq le))
  go {Δ′ = Δ′} (suc n) wfΔ wfΔ′ wfW M⊑M′ (st′ then r′₀) (s≤s le)
    | inj₁ (N₂ , N₂′ , r₁ , r₁″ , W₁ , ev₁ , wfW₁ , q₁ , N₂⊑N₂′)
    | inj₁ (s , eq)
    | inj₂ (ℓ , r₂) = inj₂ (ℓ , r₁ ++ʳ′ r₂)
  go {Δ′ = Δ′} (suc n) wfΔ wfΔ′ wfW M⊑M′ (_then_ {δ = ξ′} st′ r′₀) (s≤s le)
    | inj₁ (N₂ , N₂′ , r₁ , r₁″ , W₁ , ev₁ , wfW₁ , q₁ , N₂⊑N₂′)
    | inj₁ (s , eq)
    | inj₁ (N₃ , N₃′ , r₂ , r₂″ , rest) =
    inj₁ (N₃ , N₃′ , r₁ ++ʳ′ r₂ , castʳ E r₂″
         , evolved-cast (sym (allocs-++ʳ′ r₁ r₂)) (cong (ξ′ ∷_) eqR)
             (evolved-trans ev₁ rest))
    where
    e : runCtx r₁″ ≡ applyˢ (allocs r₁″) (apply ξ′ Δ′)
    e = runCtx≡applyˢ r₁″
    s′ = castʳ e s
    E : runCtx s′ ≡ runCtx r′₀
    E = begin
        runCtx s′
      ≡⟨ runCtx-castʳ e s ⟩
        runCtx s
      ≡⟨ sym (runCtx-++ʳ r₁″ s) ⟩
        runCtx (r₁″ ++ʳ s)
      ≡⟨ runCtx≡applyˢ (r₁″ ++ʳ s) ⟩
        applyˢ (allocs (r₁″ ++ʳ s)) (apply ξ′ Δ′)
      ≡⟨ cong (λ l → applyˢ l (apply ξ′ Δ′)) eq ⟩
        applyˢ (allocs r′₀) (apply ξ′ Δ′)
      ≡⟨ sym (runCtx≡applyˢ r′₀) ⟩
        runCtx r′₀
      ∎
    eqR : allocs r₁″ ++ allocs (s′ ++ʳ r₂″)
        ≡ allocs (r′₀ ++ʳ castʳ E r₂″)
    eqR = begin
        allocs r₁″ ++ allocs (s′ ++ʳ r₂″)
      ≡⟨ cong (allocs r₁″ ++_) (allocs-++ʳ s′ r₂″) ⟩
        allocs r₁″ ++ (allocs s′ ++ allocs r₂″)
      ≡⟨ cong (λ l → allocs r₁″ ++ (l ++ allocs r₂″))
              (allocs-castʳ e s) ⟩
        allocs r₁″ ++ (allocs s ++ allocs r₂″)
      ≡⟨ sym (++-assoc (allocs r₁″) (allocs s) (allocs r₂″)) ⟩
        (allocs r₁″ ++ allocs s) ++ allocs r₂″
      ≡⟨ cong (_++ allocs r₂″) (sym (allocs-++ʳ r₁″ s)) ⟩
        allocs (r₁″ ++ʳ s) ++ allocs r₂″
      ≡⟨ cong (_++ allocs r₂″) eq ⟩
        allocs r′₀ ++ allocs r₂″
      ≡⟨ cong (allocs r′₀ ++_) (sym (allocs-castʳ E r₂″)) ⟩
        allocs r′₀ ++ allocs (castʳ E r₂″)
      ≡⟨ sym (allocs-++ʳ r′₀ (castʳ E r₂″)) ⟩
        allocs (r′₀ ++ʳ castʳ E r₂″)
      ∎

------------------------------------------------------------------------
-- The statement
------------------------------------------------------------------------

simBack* : SimBack*
simBack* wfΔ wfΔ′ wfW M⊑M′ r′ = go (len r′) wfΔ wfΔ′ wfW M⊑M′ r′ ≤-refl
