open import TypeSafety
  using (Progress; Preservation; PreservationWf; Irreducible)
open import proof.DGG.MultiSimDef using (Sim*)
open import proof.DGG.MultiSimBackDef using (SimBack*)
open import proof.DGG.CatchupRightDef using (CatchupRight)
open import proof.DGG.CatchupLeftDef using (CatchupLeft)
open import proof.DGG.CatchupBlameDef using (CatchupBlame)
open import proof.DGG.ImprecisionTypingDef using (ImprecisionTyping)

module proof.DGG.DynamicGradualGuaranteeProof
  (sim* : Sim*)
  (simBack* : SimBack*)
  (catchupRight : CatchupRight)
  (catchupLeft : CatchupLeft)
  (catchupBlame : CatchupBlame)
  (impTyping : ImprecisionTyping)
  (progress : Progress)
  (preservation : Preservation)
  (preservationWf : PreservationWf)
  (irreducible : Irreducible)
  where

-- File Charter:
--   * THE PROOF OF `DGG` (DynamicGradualGuarantee.agda) from the
--     statements of the major lemmas, parameterized at the module level
--     (proof/DGG/PLAN.md §1).  GTLC's proof
--     (GTLC/agda/proof/DynamicGradualGuarantee.agda), with the sides
--     flipped: the LEFT term is the more precise one.
--     - part 1 (`forward`): Sim* along the left run, then CatchupRight;
--     - part 3 (`backward`): SimBack* along the right run (the right's
--       continuation from a value is `done`, by Irreducible), then
--       CatchupLeft;
--     - part 2 (`diverge`): contrapositively, `converge-back` (SimBack*,
--       then CatchupLeft at a value, CatchupBlame at blame);
--     - part 4 (`diverge-or-blame`): Progress on the reached state, typed
--       by ImprecisionTyping and preservation along the run; a value
--       contradicts the right's divergence by part 1.
--   * The final worlds are moved to `World (runCtx r) (runCtx r′)` by
--     `runCtx≡applyˢ` (`related-cast`, proof/DGG/EvolveLemmas).

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Types using (Ty)
open import Ctx using (empty)
open import proof.Ctx using (wf-empty)
open import Coercion using (Label)
open import Terms using (Term; Value; blame)
open import Reduction using (_⊢_-→*_; done; _then_; runCtx)
open import ImprecisionWorld
  using (World; ∅ʷ; WfWorld; wf-world; Joint; joint[]; Paired;
         _⊑ᵂ⟨_⟩_)
open import TermImprecision using (_∣_⊢_⊑_∶_)
open import DynamicGradualGuarantee
  using (DGG; Converges; Diverges; DivergeOrBlame; RelatedValues)
open import proof.DGG.Evolve using (applyˢ; allocs; runCtx≡applyˢ; _++ʳ_)
open import proof.DGG.EvolveLemmas
  using (_++ʳ′_; runCtx-++ʳ; runCtx-++ʳ′; related-cast)
open import proof.DGG.RunTyping preservation preservationWf
  using (⊢*; wfˢ)

------------------------------------------------------------------------
-- The initial world is well formed
------------------------------------------------------------------------

private
  no-pair : ∀ {α β} → Paired ∅ʷ α β → ∀ {X : Set} → X
  no-pair (inj₁ ())
  no-pair (inj₂ ())

wf-∅ʷ : WfWorld ∅ʷ
wf-∅ʷ = wf-world joint[] (λ π → no-pair π) (λ π π′ → no-pair π)

------------------------------------------------------------------------
-- The four parts, for a fixed pair of related closed programs
------------------------------------------------------------------------

module _ {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ ∅ʷ ⟩ A′}
    (M⊑M′ : ∅ʷ ∣ [] ⊢ M ⊑ M′ ∶ p) where

  private
    ⊢M  = proj₁ (impTyping M⊑M′)
    ⊢M′ = proj₂ (impTyping M⊑M′)

  -- part 1
  forward : ∀ {V} (r : empty ⊢ M -→* V) → Value V
    → ∃[ V′ ] Σ[ r′ ∈ empty ⊢ M′ -→* V′ ]
        (Value V′ × RelatedValues A A′ r r′)
  forward r v
      with sim* wf-empty wf-empty wf-∅ʷ M⊑M′ r
  ... | N′ , r′ , W′ , ev , wfW′ , q , N⊑N′
      with catchupRight (wfˢ wf-empty ⊢M r) (wfˢ wf-empty ⊢M′ r′)
                        wfW′ v N⊑N′
  ... | V′ , r″ , v′ , W″ , ev′ , wfW″ , q′ , V⊑V′ =
    V′ , r′ ++ʳ′ r″ , v′
    , related-cast (sym (runCtx≡applyˢ r))
        (sym (trans (runCtx-++ʳ′ r′ r″) (runCtx≡applyˢ r″)))
        (W″ , wfW″ , q′ , V⊑V′)

  -- part 3
  backward : ∀ {V′} (r′ : empty ⊢ M′ -→* V′) → Value V′
    → (∃[ V ] Σ[ r ∈ empty ⊢ M -→* V ]
         (Value V × RelatedValues A A′ r r′))
      ⊎ (∃[ ℓ ] (empty ⊢ M -→* blame ℓ))
  backward r′ v′
      with simBack* wf-empty wf-empty wf-∅ʷ M⊑M′ r′
  backward r′ v′ | inj₂ M↠blame = inj₂ M↠blame
  backward r′ v′ | inj₁ (N₂ , _ , r , (st then r″) , rest) =
    ⊥-elim (proj₁ irreducible v′ st)
  backward r′ v′ | inj₁ (N₂ , _ , r , done , W′ , ev , wfW′ , q , N₂⊑V′)
      with catchupLeft (wfˢ wf-empty ⊢M r)
                       (wfˢ wf-empty ⊢M′ (r′ ++ʳ done)) wfW′ v′ N₂⊑V′
  backward r′ v′ | inj₁ (N₂ , _ , r , done , W′ , ev , wfW′ , q , N₂⊑V′)
    | inj₁ (V , r₂ , v , W″ , ev′ , wfW″ , q′ , V⊑V′) =
    inj₁ (V , r ++ʳ′ r₂ , v
         , related-cast
             (sym (trans (runCtx-++ʳ′ r r₂) (runCtx≡applyˢ r₂)))
             (trans (sym (runCtx≡applyˢ (r′ ++ʳ done)))
                    (runCtx-++ʳ r′ done))
             (W″ , wfW″ , q′ , V⊑V′))
  backward r′ v′ | inj₁ (N₂ , _ , r , done , W′ , ev , wfW′ , q , N₂⊑V′)
    | inj₂ (ℓ , r₂) =
    inj₂ (ℓ , r ++ʳ′ r₂)

  -- the right converges, so the left converges
  converge-back : Converges M′ → Converges M
  converge-back (V′ , r′ , inj₁ v′) with backward r′ v′
  converge-back (V′ , r′ , inj₁ v′) | inj₁ (V , r , v , rel) =
    V , r , inj₁ v
  converge-back (V′ , r′ , inj₁ v′) | inj₂ (ℓ , r) =
    blame ℓ , r , inj₂ (ℓ , refl)
  converge-back (_ , r′ , inj₂ (ℓ , refl))
      with simBack* wf-empty wf-empty wf-∅ʷ M⊑M′ r′
  converge-back (_ , r′ , inj₂ (ℓ , refl)) | inj₂ (ℓ′ , r) =
    blame ℓ′ , r , inj₂ (ℓ′ , refl)
  converge-back (_ , r′ , inj₂ (ℓ , refl))
    | inj₁ (N₂ , _ , r , (st then r″) , rest) =
    ⊥-elim (proj₂ irreducible st)
  converge-back (_ , r′ , inj₂ (ℓ , refl))
    | inj₁ (N₂ , _ , r , done , W′ , ev , wfW′ , q , N₂⊑blame)
      with catchupBlame N₂⊑blame
  converge-back (_ , r′ , inj₂ (ℓ , refl))
    | inj₁ (N₂ , _ , r , done , W′ , ev , wfW′ , q , N₂⊑blame)
    | ℓ′ , r₂ =
    blame ℓ′ , r ++ʳ′ r₂ , inj₂ (ℓ′ , refl)

  -- part 2
  diverge : Diverges M → Diverges M′
  diverge div conv′ = div (converge-back conv′)

  -- part 4
  diverge-or-blame : Diverges M′ → DivergeOrBlame M
  diverge-or-blame div′ r with progress (⊢* wf-empty ⊢M r)
  diverge-or-blame div′ r | inj₁ v with forward r v
  diverge-or-blame div′ r | inj₁ v | V′ , r′ , v′ , rel =
    ⊥-elim (div′ (V′ , r′ , inj₁ v′))
  diverge-or-blame div′ r | inj₂ (inj₁ isBlame) = inj₁ isBlame
  diverge-or-blame div′ r | inj₂ (inj₂ (N′ , δ , st)) =
    inj₂ (N′ , δ , st)

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

dgg : DGG
dgg M⊑M′ =
  forward M⊑M′ , diverge M⊑M′ , backward M⊑M′ , diverge-or-blame M⊑M′
