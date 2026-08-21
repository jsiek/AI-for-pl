{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.StructuralStrictConversionProducerProbe where

-- File Charter:
--   * Checks assembly of the strict universal reveal and conceal children
--     after a relation-side producer has supplied its exact evidence.
--   * Isolates the missing live inputs: the post-bind child endpoint,
--     relation, and child-target-indexed structural provenance.
--   * Uses the canonical target-bind plan and chain-plan machinery; it does
--     not assume that a nominal target insertion commutes with every source
--     rebase in the parent relation.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyVar; ＇_; `∀; _[_]ᵗ; ⇑ᵗ)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import Conversion using (Conv↑; Conv↓; 〖_,_↑_〗)
open import CastTerms using (Term; Value; ⇑ᵗᵐ)
open import Reduction using
  (bind; applyTy; applyBody; applyStores; _∷_; [])
open import proof.TypeInTermSubst using
  (renameᵗᵐ-preserves-Value)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
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


reveal-conversion-child-assembly : ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W₁ : CTX.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {c : Conv↑ (suc Δᴿ) C B}
    {π : Δ ↪ᵗ Δ₁}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W Aₛ E q)
  → StructuralNameChainPlan {fuel = fuel} W γ Aₛ E q plan
  → Value V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTX.targetStoreʷ W₁ ≡
      applyStores (bind (＇ X) ∷ []) (CTX.targetStoreʷ W))
  → (child-target : StructuralTargetInstantiationPackage W₁ (⇑ᵗᵐ V)
      (name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
          refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        reveal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine))
  → let
         ext₁ = target-insert-bind-world-extendᴿ ins follows
         child-spine =
           name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
             refl refl ▻ⁱ
           type-transport-frame (applyBody-open-zero C) ▻ⁱ
           reveal-frame c ▻ⁱ
           reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
           type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
           mapInstantiationSpine (bind (＇ X)) spine
     in (child-endpoint : Aₛ CTX.⊑ᵂ⟨ W₁ ⟩
          applyTy (bind (＇ X)) (`∀ C))
  → (child-relation : W₁ CTI2.∣ ECR.mapCtxᴿ ext₁ γ
      ⊢² M ⊑ ⇑ᵗᵐ V ∶ child-endpoint)
  → StructuralTermProvenance
      (StructuralTargetInstantiationPackage.structural-ext child-target)
      child-relation
  → StructuralStrictChild {fuel = fuel} W₁
      (ECR.mapCtxᴿ ext₁ γ) M (⇑ᵗᵐ V) Aₛ
      (applyTy (bind (＇ X)) (`∀ C))
      (applyTy (bind (＇ X)) E) child-spine
      (ECR.transport⊑ᵂ ext₁ q) child-target
reveal-conversion-child-assembly {B = B} {C = C} {X = X} {c = c}
    plan chain-plan vV spine ins follows child-target child-endpoint
    child-relation child-provenance
    with StructuralNamePostPlan.target-bind-child plan ins follows
       | StructuralNameChainPlan.target-bind-child chain-plan ins follows
           (name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
               refl refl ▻ⁱ
             type-transport-frame (applyBody-open-zero C) ▻ⁱ
             reveal-frame c ▻ⁱ
             reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
             type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
             mapInstantiationSpine (bind (＇ X)) spine)
reveal-conversion-child-assembly {B = B} {C = C} {X = X} {c = c}
    plan chain-plan vV spine ins follows child-target child-endpoint
    child-relation child-provenance
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


conceal-conversion-child-assembly : ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W₁ : CTX.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {c : Conv↓ (suc Δᴿ) C B}
    {π : Δ ↪ᵗ Δ₁}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W Aₛ E q)
  → StructuralNameChainPlan {fuel = fuel} W γ Aₛ E q plan
  → Value V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTX.targetStoreʷ W₁ ≡
      applyStores (bind (＇ X) ∷ []) (CTX.targetStoreʷ W))
  → (child-target : StructuralTargetInstantiationPackage W₁ (⇑ᵗᵐ V)
      (name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
          refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        conceal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine))
  → let
         ext₁ = target-insert-bind-world-extendᴿ ins follows
         child-spine =
           name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
             refl refl ▻ⁱ
           type-transport-frame (applyBody-open-zero C) ▻ⁱ
           conceal-frame c ▻ⁱ
           reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
           type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
           mapInstantiationSpine (bind (＇ X)) spine
     in (child-endpoint : Aₛ CTX.⊑ᵂ⟨ W₁ ⟩
          applyTy (bind (＇ X)) (`∀ C))
  → (child-relation : W₁ CTI2.∣ ECR.mapCtxᴿ ext₁ γ
      ⊢² M ⊑ ⇑ᵗᵐ V ∶ child-endpoint)
  → StructuralTermProvenance
      (StructuralTargetInstantiationPackage.structural-ext child-target)
      child-relation
  → StructuralStrictChild {fuel = fuel} W₁
      (ECR.mapCtxᴿ ext₁ γ) M (⇑ᵗᵐ V) Aₛ
      (applyTy (bind (＇ X)) (`∀ C))
      (applyTy (bind (＇ X)) E) child-spine
      (ECR.transport⊑ᵂ ext₁ q) child-target
conceal-conversion-child-assembly {B = B} {C = C} {X = X} {c = c}
    plan chain-plan vV spine ins follows child-target child-endpoint
    child-relation child-provenance
    with StructuralNamePostPlan.target-bind-child plan ins follows
       | StructuralNameChainPlan.target-bind-child chain-plan ins follows
           (name-type-app-frame (applyBody (bind (＇ X)) C) Fin.zero
               refl refl ▻ⁱ
             type-transport-frame (applyBody-open-zero C) ▻ⁱ
             conceal-frame c ▻ⁱ
             reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
             type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
             mapInstantiationSpine (bind (＇ X)) spine)
conceal-conversion-child-assembly {B = B} {C = C} {X = X} {c = c}
    plan chain-plan vV spine ins follows child-target child-endpoint
    child-relation child-provenance
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
