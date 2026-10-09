open import TypeSafety using (Preservation; PreservationWf)
open import proof.DGG.SimDef using (Sim)
open import proof.DGG.ImprecisionTypingDef using (ImprecisionTyping)

module proof.DGG.MultiSimProof
  (sim : Sim)
  (impTyping : ImprecisionTyping)
  (preservation : Preservation)
  (preservationWf : PreservationWf)
  where

-- File Charter:
--   * THE PROOF OF `Sim*` (MultiSimDef.agda) from `Sim`, by induction on
--     the left run (GTLC's `sim*`, flipped).  Parameterized at the
--     module level (proof/DGG/PLAN.md §1).
--   * Each left step is simulated by `Sim`; the right runs are
--     concatenated (`_++ʳ′_`) and the evolutions composed
--     (`evolved-trans`, proof/DGG/EvolveLemmas).  The `WfCtx` premises
--     of the recursive call come from preservation along the steps
--     (proof/DGG/RunTyping), the typings from ImprecisionTyping.

open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans)

open import Reduction using (done; _then_)
open import ImprecisionWorld using (World)
open import proof.DGG.MultiSimDef using (Sim*)
open import proof.DGG.Evolve using (_⟿[_∣_]_; ev-done)
open import proof.DGG.EvolveLemmas
  using (_++ʳ′_; allocs-++ʳ′; evolved-trans; evolved-cast; ⟿-κʷ)
open import proof.DGG.RunTyping preservation preservationWf using (wfˢ)

sim* : Sim*
sim* {W = W} {M′ = M′} wfΔ wfΔ′ wfW κ[] M⊑M′ done =
  M′ , done , W , ev-done , wfW , _ , M⊑M′
sim* wfΔ wfΔ′ wfW κ[] M⊑M′ (st then r)
    with sim wfΔ wfΔ′ wfW κ[] M⊑M′ st
... | N₁′ , r₁′ , W₁ , ev₁ , wfW₁ , q₁ , N₁⊑N₁′
    with sim* (preservationWf wfΔ (proj₁ (impTyping M⊑M′)) st)
              (wfˢ wfΔ′ (proj₂ (impTyping M⊑M′)) r₁′)
              wfW₁ (⟿-κʷ ev₁ κ[]) N₁⊑N₁′ r
... | N₂′ , r₂′ , rest =
  N₂′ , r₁′ ++ʳ′ r₂′
  , evolved-cast refl (sym (allocs-++ʳ′ r₁′ r₂′))
      (evolved-trans ev₁ rest)
