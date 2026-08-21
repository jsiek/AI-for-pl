module proof.DGG.Catchup.StructuralTermReplayProof where

-- File Charter:
--   * Extracts exact source-wrapper replays from recursive structural term
--     provenance.
--   * Uses the companion insertion and post-bind rebase stored at every bind;
--     no universal insertion/rebase commutation theorem is assumed.

open import Data.Product using (_,_)
open import Data.Maybe using (nothing)
open import Types using (Ty)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using (Term)
open import Reduction using (StoreChanges)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralTermProvenanceDef


structural-reveal-replay-provenance : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ?}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A′ CTX.⊑ᵂ⟨ W ⟩ B}
    {mono : CTX.ImpEnvMono W Wᵖ}
    {rb : CTX.RebaseAtᴸ W Wᵖ Xᴸ?}
    {sc : CTX.SameCtx γ γᵖ}
    {c : Conv↑ Δᴸ A A′}
    {c⊢ : CTX.sourceStoreʷ W Conversion.⊢↑[ Xᴸ? ] c}
    {prem : Wᵖ CTI2.∣ γᵖ ⊢² M ⊑ N ∶ p}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → StructuralTermProvenance plan
      (CTI2.reveal⊑² mono rb sc c⊢ prem q)
  → StructuralRebaseAtᴸReplay plan rb
structural-reveal-replay-provenance structural-[]
    term-provenance-[] =
  rebaseᴸ-replay-[]
structural-reveal-replay-provenance (structural-keep plan)
    (term-provenance-keep provenance) =
  rebaseᴸ-replay-keep
    (structural-reveal-replay-provenance plan provenance)
structural-reveal-replay-provenance
    (structural-bind ins follows plan)
    (term-provenance-bind
      (Wᵖ₁ , insᵖ , rb₁ , child-provenance) provenance) =
  rebaseᴸ-replay-bind insᵖ rb₁
    (structural-reveal-replay-provenance plan provenance)


structural-conceal-replay-provenance : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ?}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A′ CTX.⊑ᵂ⟨ W ⟩ B}
    {mono : CTX.ImpEnvMono W Wᵖ}
    {rb : CTX.TagRebaseAtᴸ Wᵖ W Xᴸ? nothing}
    {sc : CTX.SameCtx γ γᵖ}
    {c : Conv↓ Δᴸ A A′}
    {c⊢ : CTX.sourceStoreʷ W Conversion.⊢↓[ Xᴸ? ] c}
    {prem : Wᵖ CTI2.∣ γᵖ ⊢² M ⊑ N ∶ p}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → StructuralTermProvenance plan
      (CTI2.conceal⊑² mono rb sc c⊢ prem q)
  → StructuralTagRebaseAtᴸReplay plan rb
structural-conceal-replay-provenance structural-[]
    term-provenance-[] =
  tag-rebase-[]
structural-conceal-replay-provenance (structural-keep plan)
    (term-provenance-keep provenance) =
  tag-rebase-keep
    (structural-conceal-replay-provenance plan provenance)
structural-conceal-replay-provenance
    (structural-bind ins follows plan)
    (term-provenance-bind
      (Wᵖ₁ , insᵖ , rb₁ , child-provenance) provenance) =
  tag-rebase-bind insᵖ rb₁
    (structural-conceal-replay-provenance plan provenance)
