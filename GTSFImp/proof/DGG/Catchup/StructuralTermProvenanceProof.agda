module proof.DGG.Catchup.StructuralTermProvenanceProof where

-- File Charter:
--   * Transports exact structural term provenance through target casts and
--     eliminates source casts, Λ rules, reveals, and conceals.
--   * Recovers the exact premise-plan certificate required by recursive
--     structural name-instantiation replay.

import Data.Fin as Fin
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (suc)
open import Data.Product using (_,_)

open import Types using (Ty; TyVar; NonVar; _∈ᵗ_; `∀)
open import Imprecision using (X⊑★)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⊢_⦂_; Λ_)
open import Conversion using (Conv↑; Conv↓)
open import Reduction using (StoreChanges)
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldLiftLeftProof
open import proof.DGG.Catchup.StructuralWorldSmartLiftDef
open import proof.DGG.Catchup.StructuralWorldSmartLiftProof
open import proof.DGG.Catchup.StructuralWorldRebaseProof
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseProof
open import proof.DGG.Catchup.StructuralTermProvenanceDef
open import proof.DGG.Catchup.StructuralTermReplayProof


target-cast-provenance : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {c : ν ⊢ B ∼ B′}
    {p : A CTX.⊑ᵂ⟨ W ⟩ B}
    {q : A CTX.⊑ᵂ⟨ W ⟩ B′}
    {plan : StructuralWorldExtendᴿ χs W W′}
    {rel : W CTI2.∣ γ ⊢² M ⊑ N ∶ p}
  → StructuralTermProvenance plan rel
  → StructuralTermProvenance plan (CTI2.⊑cast² c rel q)
target-cast-provenance term-provenance-[] = term-provenance-[]
target-cast-provenance (term-provenance-keep provenance) =
  term-provenance-keep (target-cast-provenance provenance)
target-cast-provenance
    (term-provenance-bind insertion-provenance provenance) =
  term-provenance-bind insertion-provenance
    (target-cast-provenance provenance)


source-cast-premise-provenance : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ A ∼ A′}
    {p : A CTX.⊑ᵂ⟨ W ⟩ B}
    {q : A′ CTX.⊑ᵂ⟨ W ⟩ B}
    {plan : StructuralWorldExtendᴿ χs W W′}
    {prem : W CTI2.∣ γ ⊢² M ⊑ N ∶ p}
  → StructuralTermProvenance plan (CTI2.cast⊑² c prem q)
  → StructuralTermProvenance plan prem
source-cast-premise-provenance term-provenance-[] = term-provenance-[]
source-cast-premise-provenance (term-provenance-keep provenance) =
  term-provenance-keep (source-cast-premise-provenance provenance)
source-cast-premise-provenance
    (term-provenance-bind insertion-provenance provenance) =
  term-provenance-bind insertion-provenance
    (source-cast-premise-provenance provenance)


plain-Λ-premise-provenance : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W}
    {γᴸ : CTX.CtxImp (CTX.liftWorldLeft W)}
    {V : Term (suc Δᴸ)} {M : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
    {p : A CTX.⊑ᵂ⟨ CTX.liftWorldLeft W ⟩ B}
    {q : `∀ A CTX.⊑ᵂ⟨ W ⟩ B}
    {Anv : NonVar A} {z∈A : Fin.zero ∈ᵗ A}
    {liftγ : CTX.LiftCtxᴸ X⊑★ γ γᴸ}
    {vV : Value V}
    {M⊢ : ⟨ Δᴿ , CTX.targetStoreʷ W , CTX.tgtCtxʷ γ ⟩ ⊢ M ⦂ B}
    {prem : CTX.liftWorldLeft W CTI2.∣ γᴸ ⊢² V ⊑ M ∶ p}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → StructuralTermProvenance plan
      (CTI2.Λ⊑² Anv z∈A liftγ vV M⊢ prem q)
  → StructuralTermProvenance (structural-lift-left plan X⊑★) prem
plain-Λ-premise-provenance structural-[] term-provenance-[] =
  term-provenance-[]
plain-Λ-premise-provenance (structural-keep plan)
    (term-provenance-keep provenance) =
  term-provenance-keep (plain-Λ-premise-provenance plan provenance)
plain-Λ-premise-provenance (structural-bind ins follows plan)
    (term-provenance-bind insertion-provenance provenance) =
  term-provenance-bind insertion-provenance
    (plain-Λ-premise-provenance plan provenance)


smart-Λ-premise-provenance : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : CTX.World (suc Δᴸ) Δᴿ Δᵐ}
    {γ : CTX.CtxImp W} {γᵐ : CTX.CtxImp Wᵐ}
    {V : Term (suc Δᴸ)} {M : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
    {p : A CTX.⊑ᵂ⟨ Wᵐ ⟩ B}
    {q : `∀ A CTX.⊑ᵂ⟨ W ⟩ B}
    {Anv : NonVar A} {z∈A : Fin.zero ∈ᵗ A}
    {liftW : CTX.SmartCommaLiftᴸ W Wᵐ}
    {liftγ : CTX.SmartLiftCtxᴸ γ γᵐ}
    {vV : Value V}
    {M⊢ : ⟨ Δᴿ , CTX.targetStoreʷ W , CTX.tgtCtxʷ γ ⟩ ⊢ M ⦂ B}
    {prem : Wᵐ CTI2.∣ γᵐ ⊢² V ⊑ M ∶ p}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → StructuralTermProvenance plan
      (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV M⊢ prem q)
  → let child = structural-smart-liftᴸ plan liftW
     in StructuralTermProvenance
          (StructuralSmartLiftᴸResult.premise-plan child) prem
smart-Λ-premise-provenance {liftW = CTX.smart-merge-alias guard}
    plan provenance =
  ⊥-elim (TE.smartAliasGuard-impossible guard)
smart-Λ-premise-provenance {liftW = CTX.smart-fresh-behind guard}
    structural-[] term-provenance-[] =
  term-provenance-[]
smart-Λ-premise-provenance {liftW = CTX.smart-fresh-behind guard}
    (structural-keep plan)
    (term-provenance-keep provenance) =
  term-provenance-keep (smart-Λ-premise-provenance plan provenance)
smart-Λ-premise-provenance {liftW = CTX.smart-fresh-behind guard}
    (structural-bind ins follows plan)
    (term-provenance-bind insertion-provenance provenance) =
  term-provenance-bind insertion-provenance
    (smart-Λ-premise-provenance
      {liftW = CTX.smart-fresh-behind
        (TE.smartFreshGuardInsert ins guard)}
      plan provenance)


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
