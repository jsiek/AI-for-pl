{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.StructuralStrictLambdaReadyProbe where

-- File Charter:
--   * Checks the value-ready strict child interface for a target β-Λ step.
--   * Moves the administrative reveal from the child term to the front of
--     its pending spine, preserving the value-only recursive worker.
--   * Assumes the exact relation, chain, typing, and provenance that a live
--     Λ producer must establish.  This module changes no live proof surface.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Nat.Properties using (n<1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyVar; ＇_; `∀; _[_]ᵗ; ⇑ᵗ)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import Conversion using (〖_,_↑_〗)
import CastTerms as CT
open import CastTerms using (Term; Value; Λ_; _↑_)
open import Reduction using (bind; applyTy; applyStores; _∷_; [])
open import proof.TypeSafety.Preservation using (replace-zero-open)
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralValueInstantiationCastMassDef
open import
  proof.DGG.Catchup.StructuralValueInstantiationSpineCastMassProof
    using (spine-cast-mass-map)
open import proof.DGG.Catchup.StructuralValueInstantiationRankDef
open import proof.DGG.Catchup.StructuralValueInstantiationRankProof using
  (_<ʳ_; rank-name<; nameFrames-map)
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetInstantiationProof using
  (structural-target-frame)
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Catchup.StructuralTargetFrameAbsorptionDef
open import proof.DGG.Catchup.StructuralSpineTypingDef
open import proof.DGG.Catchup.StructuralTermProvenanceDef
open import proof.DGG.Catchup.StructuralStrictViewSurfaceDef
open import proof.DGG.Catchup.StructuralWorldExtendProof using
  (target-insert-bind-world-extendᴿ)


lambda-ready-child-spine : ∀ {Δ} {B : Ty (suc Δ)} {E : Ty Δ}
    {X : TyVar Δ}
  → InstantiationSpine (B [ ＇ X ]ᵗ) E
  → InstantiationSpine B (applyTy (bind (＇ X)) E)
lambda-ready-child-spine {B = B} {X = X} spine =
  reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
  type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
  mapInstantiationSpine (bind (＇ X)) spine


lambda-ready-mass-equal : ∀ {Δ} {B : Ty (suc Δ)}
    {E : Ty Δ} {V : Term (suc Δ)} {X : TyVar Δ}
    (vV : Value V)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → pendingCastMass vV
      (lambda-ready-child-spine {B = B} {X = X} spine) ≡
      pendingCastMass (CT.Λ vV)
        (name-type-app-frame B X refl refl ▻ⁱ spine)
lambda-ready-mass-equal {X = X} vV spine
    rewrite spine-cast-mass-map (bind (＇ X)) spine =
  refl


lambda-ready-rank-decreases : ∀ {Δ} {B : Ty (suc Δ)}
    {E : Ty Δ} {V : Term (suc Δ)} {X : TyVar Δ}
    (vV : Value V)
    (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → pendingRank vV
      (lambda-ready-child-spine {B = B} {X = X} spine) <ʳ
      pendingRank (CT.Λ vV)
        (name-type-app-frame B X refl refl ▻ⁱ spine)
lambda-ready-rank-decreases {X = X} vV spine
    rewrite nameFrames-map (bind (＇ X)) spine =
  rank-name< (n<1+n (nameFrames spine))


lambda-ready-child-assembly : ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W₁ : CTX.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term (suc Δᴿ)}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {π : Δ ↪ᵗ Δ₁}
    {p : A CTX.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTX.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W A E q)
  → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
  → W CTI2.∣ γ ⊢² M ⊑ Λ V ∶ p
  → Value M
  → (vV : Value V)
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → TargetFrameAbsorptionChain W γ A
      (name-type-app-frame B X refl refl ▻ⁱ spine) q
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame B X refl refl ▻ⁱ spine)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTX.targetStoreʷ W₁ ≡
      applyStores (bind (＇ X) ∷ []) (CTX.targetStoreʷ W))
  → (child-target : StructuralTargetInstantiationPackage W₁
      (V ↑ 〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)
      (type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine))
  → let ext₁ = target-insert-bind-world-extendᴿ ins follows
     in (child-endpoint : A CTX.⊑ᵂ⟨ W₁ ⟩ B)
  → (child-relation : W₁ CTI2.∣ ECR.mapCtxᴿ ext₁ γ
      ⊢² M ⊑ V ∶ child-endpoint)
  → (child-plan : StructuralNamePostPlan W₁ A
      (applyTy (bind (＇ X)) E) (ECR.transport⊑ᵂ ext₁ q))
  → StructuralNameChainPlan {fuel = fuel} W₁ (ECR.mapCtxᴿ ext₁ γ) A
      (applyTy (bind (＇ X)) E) (ECR.transport⊑ᵂ ext₁ q) child-plan
  → StructuralTermProvenance
      (StructuralTargetInstantiationPackage.structural-ext
        (structural-target-frame {V = V}
          {frame = reveal-frame
            (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)} child-target))
      child-relation
  → TargetFrameAbsorptionChain W₁ (ECR.mapCtxᴿ ext₁ γ) A
      (lambda-ready-child-spine {B = B} {X = X} spine)
      (ECR.transport⊑ᵂ ext₁ q)
  → SpineTypedʷ {fuel = fuel} W₁
      (lambda-ready-child-spine {B = B} {X = X} spine)
  → StructuralStrictChild {fuel = fuel} W₁
      (ECR.mapCtxᴿ ext₁ γ) M V A B (applyTy (bind (＇ X)) E)
      (lambda-ready-child-spine {B = B} {X = X} spine)
      (ECR.transport⊑ᵂ ext₁ q)
      (structural-target-frame {V = V}
        {frame = reveal-frame
          (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗)} child-target)
lambda-ready-child-assembly plan chain-plan rel vM vV spine chain typed
    ins follows child-target child-endpoint child-relation child-plan
    child-chain-plan child-provenance child-chain child-typed =
  record
    { child-endpoint = child-endpoint
    ; child-value = vV
    ; child-plan = child-plan
    ; child-chain-plan = child-chain-plan
    ; child-relation = child-relation
    ; child-provenance = child-provenance
    ; child-chain = child-chain
    ; child-typed = child-typed
    }
