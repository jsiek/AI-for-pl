module proof.DGG.notes.probes.StructuralStrictAllocationProducerProbe where

-- File Charter:
--   * Checks assembly of the allocation-shaped strict Lambda and generated
--     children after their relational producer has supplied exact evidence.
--   * Isolates the missing live surface inputs: the child endpoint, relation,
--     value (for Lambda), and child-target-indexed structural provenance.
--   * Uses the existing target-bind plan and chain-plan machinery; it does not
--     synthesize target-insertion provenance.

import Data.Fin as Fin
open import Data.Empty using (⊥)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using
  (Ty; TyVar; ★; ＇_; _[_]ᵗ; ⇑ᵗ)
open import Consistency using (_↪ᵗ_; wk↪ᵗ; Env∼; genᵐ; _⊢_∼_)
open import Conversion using (replaceTy; 〖_,_↑_〗)
import CastTerms as CT
open import CastTerms using
  (Term; Value; _↑_; ⇑ᵗᵐ)
open import Reduction using
  (bind; applyTy; applyStores; _∷_; [])
open import proof.TypeInTermSubst using
  (renameᵗᵐ-preserves-Value)
open import proof.TypeSafety.Preservation using
  (replace-zero-open)
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Catchup.StructuralTargetFrameAbsorptionDef
open import proof.DGG.Catchup.StructuralSpineTypingDef
open import proof.DGG.Catchup.StructuralTermProvenanceDef
open import proof.DGG.Catchup.StructuralStrictViewSurfaceDef


lambda-star-child-not-value : ∀ {Δ} {V : Term (suc Δ)} {X : TyVar Δ}
  → Value (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ ★ 〗)
  → ⊥
lambda-star-child-not-value (vV CT.↑ ())


lambda-allocation-child-assembly : ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W₁ : CTX.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term (suc Δᴿ)}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {π : Δ ↪ᵗ Δ₁}
    {q : A CTX.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W A E q)
  → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTX.targetStoreʷ W₁ ≡
      applyStores (bind (＇ X) ∷ []) (CTX.targetStoreʷ W))
  → (child-target : StructuralTargetInstantiationPackage W₁
      (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)
      (type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine))
  → let
         ext₁ = target-insert-bind-world-extendᴿ ins follows
         child-spine =
           type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
           mapInstantiationSpine (bind (＇ X)) spine
     in (child-endpoint : A CTX.⊑ᵂ⟨ W₁ ⟩
          replaceTy Fin.zero (⇑ᵗ (＇ X)) B)
  → Value (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)
  → (child-relation : W₁ CTI2.∣ ECR.mapCtxᴿ ext₁ γ
      ⊢² M ⊑ V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗 ∶ child-endpoint)
  → StructuralTermProvenance
      (StructuralTargetInstantiationPackage.structural-ext child-target)
      child-relation
  → StructuralStrictChild {fuel = fuel} W₁
      (ECR.mapCtxᴿ ext₁ γ) M
      (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)
      A (replaceTy Fin.zero (⇑ᵗ (＇ X)) B)
      (applyTy (bind (＇ X)) E) child-spine
      (ECR.transport⊑ᵂ ext₁ q) child-target
lambda-allocation-child-assembly {B = B} {X = X}
    plan chain-plan spine ins follows
    child-target child-endpoint child-value child-relation
    child-provenance
    with StructuralNamePostPlan.target-bind-child plan ins follows
       | StructuralNameChainPlan.target-bind-child chain-plan ins follows
           (type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
             mapInstantiationSpine (bind (＇ X)) spine)
lambda-allocation-child-assembly {B = B} {X = X}
    plan chain-plan spine ins follows
    child-target child-endpoint child-value child-relation
    child-provenance
    | child-plan
    | child-chain , (child-typed , child-chain-plan) =
  record
    { child-endpoint = child-endpoint
    ; child-value = child-value
    ; child-plan = child-plan
    ; child-chain-plan = child-chain-plan
    ; child-relation = child-relation
    ; child-provenance = child-provenance
    ; child-chain = child-chain
    ; child-typed = child-typed
    }


gen-allocation-child-assembly : ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W₁ : CTX.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {Aₛ : Ty Δᴸ} {A : Ty Δᴿ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ} {μ : Env∼ Δᴿ}
    {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B} {π : Δ ↪ᵗ Δ₁}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W Aₛ E q)
  → StructuralNameChainPlan {fuel = fuel} W γ Aₛ E q plan
  → Value V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTX.targetStoreʷ W₁ ≡
      applyStores (bind (＇ X) ∷ []) (CTX.targetStoreʷ W))
  → (child-target : StructuralTargetInstantiationPackage W₁ (⇑ᵗᵐ V)
      (cast-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine))
  → let
         ext₁ = target-insert-bind-world-extendᴿ ins follows
         child-spine =
           cast-frame c ▻ⁱ
           reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
           type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
           mapInstantiationSpine (bind (＇ X)) spine
     in (child-endpoint : Aₛ CTX.⊑ᵂ⟨ W₁ ⟩ ⇑ᵗ A)
  → (child-relation : W₁ CTI2.∣ ECR.mapCtxᴿ ext₁ γ
      ⊢² M ⊑ ⇑ᵗᵐ V ∶ child-endpoint)
  → StructuralTermProvenance
      (StructuralTargetInstantiationPackage.structural-ext child-target)
      child-relation
  → StructuralStrictChild {fuel = fuel} W₁
      (ECR.mapCtxᴿ ext₁ γ) M (⇑ᵗᵐ V) Aₛ (⇑ᵗ A)
      (applyTy (bind (＇ X)) E) child-spine
      (ECR.transport⊑ᵂ ext₁ q) child-target
gen-allocation-child-assembly {B = B} {X = X} {c = c}
    plan chain-plan vV spine ins follows
    child-target child-endpoint child-relation child-provenance
    with StructuralNamePostPlan.target-bind-child plan ins follows
       | StructuralNameChainPlan.target-bind-child chain-plan ins follows
           (cast-frame c ▻ⁱ
             reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
             type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
             mapInstantiationSpine (bind (＇ X)) spine)
gen-allocation-child-assembly {B = B} {X = X} {c = c}
    plan chain-plan vV spine ins follows
    child-target child-endpoint child-relation child-provenance
    | child-plan
    | child-chain , (child-typed , child-chain-plan) =
  record
    { child-endpoint = child-endpoint
    ; child-value = renameᵗᵐ-preserves-Value wk↪ᵗ vV
    ; child-plan = child-plan
    ; child-chain-plan = child-chain-plan
    ; child-relation = child-relation
    ; child-provenance = child-provenance
    ; child-chain = child-chain
    ; child-typed = child-typed
    }
