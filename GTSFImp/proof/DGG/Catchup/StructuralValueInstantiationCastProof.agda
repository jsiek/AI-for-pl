module
  proof.DGG.Catchup.StructuralValueInstantiationCastProof where

-- File Charter:
--   * Replays a source inert-cast rule at a structural trace endpoint.
--   * Keeps target-frame evaluation in the target normalization phase.

open import Types using (Ty)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Inert; _⟨_⟩)
open import Reduction using (StoreChanges)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof


structural-inert-cast-replay : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {F : Term Δᴿ′}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴸ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ B}
    {q : A′ CTI2.⊑ᵂ⟨ W ⟩ B}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (c : ν ⊢ A ∼ A′)
  → Inert c
  → W′ CTI2.∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
      ⊢² M ⊑ F ∶
        ECR.transport⊑ᵂ (structural-world-extendᴿ plan) p
  → W′ CTI2.∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
      ⊢² M ⟨ c ⟩ ⊑ F ∶
        ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q
structural-inert-cast-replay plan c inert rel =
  CTI2.cast⊑² c rel
    (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) _)
