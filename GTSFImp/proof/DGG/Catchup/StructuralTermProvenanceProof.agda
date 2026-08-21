module proof.DGG.Catchup.StructuralTermProvenanceProof where

-- File Charter:
--   * Synthesizes recursive structural term provenance from the canonical
--     per-insertion provenance provider.
--   * Follows the structural keep/bind trace without assuming a generic
--     insertion/rebase commutation theorem.

open import Types using (Ty)
open import CastTerms using (Term)
open import Reduction using (StoreChanges)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.TargetExtend as TE
open import proof.DGG.TransportTermImprecisionDef using
  (TargetInsertProvenanceᵀ)
open import proof.DGG.Catchup.StructuralWorldExtendDef using
  (StructuralWorldExtendᴿ; structural-[]; structural-keep;
   structural-bind)
open import proof.DGG.Catchup.StructuralTermProvenanceDef


structural-term-provenance : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → TargetInsertProvenanceᵀ
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (rel : W CTI2.∣ γ ⊢² M ⊑ N ∶ p)
  → StructuralTermProvenance plan rel
structural-term-provenance target-provenance structural-[] rel =
  term-provenance-[]
structural-term-provenance target-provenance
    (structural-keep plan) rel =
  term-provenance-keep
    (structural-term-provenance target-provenance plan rel)
structural-term-provenance target-provenance
    (structural-bind {W₁ = W₁} ins follows plan) rel =
  term-provenance-bind provenance
    (structural-term-provenance target-provenance plan
      (TE.⊢²-target-insert W₁ ins rel provenance))
  where
  provenance = target-provenance W₁ ins rel
