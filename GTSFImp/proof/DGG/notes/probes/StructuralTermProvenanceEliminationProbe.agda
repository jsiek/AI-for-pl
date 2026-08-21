{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.StructuralTermProvenanceEliminationProbe where

-- File Charter:
--   * Tests elimination of exact structural term provenance through the live
--     one-sided source reveal and conceal rules.
--   * Recovers the premise-plan certificate used by recursive StructuralName
--     replay without a universal target-insertion provenance provider.
--   * Covers identity and pivoted source rebases through generic eliminators
--     and constructor-specialized corollaries.

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)

open import Types using (Ty; TyVar)
open import CastTerms using (Term)
open import Conversion using (Conv↑; Conv↓)
open import Reduction using (StoreChanges)
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldRebaseProof
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseProof
open import proof.DGG.Catchup.StructuralTermProvenanceDef
open import proof.DGG.Catchup.StructuralTermReplayProof


reveal-premise-provenance : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? : Maybe (TyVar Δᴸ)}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A′ CTX.⊑ᵂ⟨ W ⟩ B}
    {mono : CTX.ImpEnvMono W Wᵖ}
    {rb : CTX.RebaseAtᴸ W Wᵖ Xᴸ?}
    {sc : CTX.SameCtx γ γᵖ}
    {c : Conv↑ Δᴸ A A′}
    {c⊢ : CTX.sourceStoreʷ W Conv.⊢↑[ Xᴸ? ] c}
    {prem : Wᵖ CTI2.∣ γᵖ ⊢² M ⊑ N ∶ p}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (provenance : StructuralTermProvenance plan
      (CTI2.reveal⊑² mono rb sc c⊢ prem q))
  → let replay = structural-reveal-replay-provenance plan provenance
        child = structural-rebase-atᴸ plan rb replay
     in StructuralTermProvenance
          (StructuralRebaseAtᴸResult.premise-plan child) prem
reveal-premise-provenance structural-[] term-provenance-[] =
  term-provenance-[]
reveal-premise-provenance (structural-keep plan)
    (term-provenance-keep provenance) =
  term-provenance-keep (reveal-premise-provenance plan provenance)
reveal-premise-provenance (structural-bind ins follows plan)
    (term-provenance-bind
      (Wᵖ₁ , insᵖ , rb₁ , child-provenance) provenance) =
  term-provenance-bind child-provenance
    (reveal-premise-provenance plan provenance)


conceal-premise-provenance : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? : Maybe (TyVar Δᴸ)}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A′ CTX.⊑ᵂ⟨ W ⟩ B}
    {mono : CTX.ImpEnvMono W Wᵖ}
    {rb : CTX.TagRebaseAtᴸ Wᵖ W Xᴸ? nothing}
    {sc : CTX.SameCtx γ γᵖ}
    {c : Conv↓ Δᴸ A A′}
    {c⊢ : CTX.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c}
    {prem : Wᵖ CTI2.∣ γᵖ ⊢² M ⊑ N ∶ p}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (provenance : StructuralTermProvenance plan
      (CTI2.conceal⊑² mono rb sc c⊢ prem q))
  → let replay = structural-conceal-replay-provenance plan provenance
        child = structural-tag-rebase-atᴸ plan rb replay
     in StructuralTermProvenance
          (StructuralTagRebaseAtᴸResult.premise-plan child) prem
conceal-premise-provenance structural-[] term-provenance-[] =
  term-provenance-[]
conceal-premise-provenance (structural-keep plan)
    (term-provenance-keep provenance) =
  term-provenance-keep (conceal-premise-provenance plan provenance)
conceal-premise-provenance (structural-bind ins follows plan)
    (term-provenance-bind
      (Wᵖ₁ , insᵖ , rb₁ , child-provenance) provenance) =
  term-provenance-bind child-provenance
    (conceal-premise-provenance plan provenance)


reveal-premise-provenance-by-form : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? : Maybe (TyVar Δᴸ)}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A′ CTX.⊑ᵂ⟨ W ⟩ B}
    {mono : CTX.ImpEnvMono W Wᵖ}
    {sc : CTX.SameCtx γ γᵖ}
    {c : Conv↑ Δᴸ A A′}
    {c⊢ : CTX.sourceStoreʷ W Conv.⊢↑[ Xᴸ? ] c}
    {prem : Wᵖ CTI2.∣ γᵖ ⊢² M ⊑ N ∶ p}
  → (rb : CTX.RebaseAtᴸ W Wᵖ Xᴸ?)
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (provenance : StructuralTermProvenance plan
      (CTI2.reveal⊑² mono rb sc c⊢ prem q))
  → let replay = structural-reveal-replay-provenance plan provenance
        child = structural-rebase-atᴸ plan rb replay
     in StructuralTermProvenance
          (StructuralRebaseAtᴸResult.premise-plan child) prem
reveal-premise-provenance-by-form CTX.rebase-idᴸ plan provenance =
  reveal-premise-provenance plan provenance
reveal-premise-provenance-by-form (CTX.rebase-varᴸ rb) plan provenance =
  reveal-premise-provenance plan provenance
reveal-premise-provenance-by-form
    (CTX.rebase-onlyᴸ mark disaligned represented) plan provenance =
  reveal-premise-provenance plan provenance


conceal-premise-provenance-by-form : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? : Maybe (TyVar Δᴸ)}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A′ CTX.⊑ᵂ⟨ W ⟩ B}
    {mono : CTX.ImpEnvMono W Wᵖ}
    {sc : CTX.SameCtx γ γᵖ}
    {c : Conv↓ Δᴸ A A′}
    {c⊢ : CTX.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c}
    {prem : Wᵖ CTI2.∣ γᵖ ⊢² M ⊑ N ∶ p}
  → (rb : CTX.TagRebaseAtᴸ Wᵖ W Xᴸ? nothing)
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (provenance : StructuralTermProvenance plan
      (CTI2.conceal⊑² mono rb sc c⊢ prem q))
  → let replay = structural-conceal-replay-provenance plan provenance
        child = structural-tag-rebase-atᴸ plan rb replay
     in StructuralTermProvenance
          (StructuralTagRebaseAtᴸResult.premise-plan child) prem
conceal-premise-provenance-by-form CTX.tag-rebase-idᴸ plan provenance =
  conceal-premise-provenance plan provenance
conceal-premise-provenance-by-form
    (CTX.tag-rebase-onlyᴸ mark disaligned represented) plan provenance =
  conceal-premise-provenance plan provenance
