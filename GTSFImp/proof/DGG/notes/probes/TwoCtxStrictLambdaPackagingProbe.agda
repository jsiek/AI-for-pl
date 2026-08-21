{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxStrictLambdaPackagingProbe where

-- File Charter:
--   * Checks the live value-ready strict-Lambda assembly boundary after the
--     two-Ctx probe has constructed the exact beta/alpha relation spine.
--   * Derives the child post-plan, chain-plan, frame-absorption chain, spine
--     typing, and value from existing structural inputs.
--   * Isolates the first missing migration theorem: a structural
--     correspondence taking the two-Ctx endpoint/relation into an already
--     existing live world, followed by provenance for the exact child target.
--     It neither constructs a live World nor resolves an administrative name.

open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyVar; ＇_; _[_]ᵗ)
open import Consistency using (_↪ᵗ_; wk↪ᵗ)
open import CastTerms using (Term; Value)
open import Reduction using
  (bind; applyTy; applyStores; _∷_; [])
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
import proof.DGG.notes.probes.TwoCtxStrictLambdaProducerProbe as Raw
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Catchup.StructuralTargetFrameAbsorptionDef
open import proof.DGG.Catchup.StructuralSpineTypingDef
open import proof.DGG.Catchup.StructuralTermProvenanceDef
open import proof.DGG.Catchup.StructuralStrictViewSurfaceDef


value-ready-Λ-child-assembly : ∀ {fuel Δᴸ Δᴿ Δ Δ₁}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W₁ : CTX.World Δᴸ (suc Δᴿ) Δ₁}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term (suc Δᴿ)}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {π : Δ ↪ᵗ Δ₁}
    {q : A CTX.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W A E q)
  → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
  → Value V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (ins : TE.TargetInsert wk↪ᵗ π W W₁)
  → (follows : CTX.targetStoreʷ W₁ ≡
      applyStores (bind (＇ X) ∷ []) (CTX.targetStoreʷ W))
  → (child-target : StructuralTargetInstantiationPackage W₁ V
      (lambda-ready-child-spine {B = B} {X = X} spine))
  → let
         ext₁ = target-insert-bind-world-extendᴿ ins follows
         child-spine =
           lambda-ready-child-spine {B = B} {X = X} spine
     in (child-endpoint : A CTX.⊑ᵂ⟨ W₁ ⟩ B)
  → (child-relation : W₁ CTI2.∣ ECR.mapCtxᴿ ext₁ γ
      ⊢² M ⊑ V ∶ child-endpoint)
  → StructuralTermProvenance
      (StructuralTargetInstantiationPackage.structural-ext child-target)
      child-relation
  → StructuralStrictChild {fuel = fuel} W₁
      (ECR.mapCtxᴿ ext₁ γ) M V A B
      (applyTy (bind (＇ X)) E) child-spine
      (ECR.transport⊑ᵂ ext₁ q) child-target
value-ready-Λ-child-assembly {B = B} {X = X}
    plan chain-plan vV spine ins follows child-target
    child-endpoint child-relation child-provenance
    with StructuralNamePostPlan.target-bind-child plan ins follows
       | StructuralNameChainPlan.target-bind-child chain-plan ins follows
           (lambda-ready-child-spine {B = B} {X = X} spine)
value-ready-Λ-child-assembly {B = B} {X = X}
    plan chain-plan vV spine ins follows child-target
    child-endpoint child-relation child-provenance
    | child-plan
    | child-chain , (child-typed , child-chain-plan) =
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


-- Constructible live fields, once a live endpoint/relation/provenance triple
-- exists:
--
--   child-value       -- the value-ready target Lambda body
--   child-plan        -- StructuralNamePostPlan.target-bind-child
--   child-chain-plan  -- StructuralNameChainPlan.target-bind-child
--   child-chain       -- same target-bind-child result
--   child-typed       -- same target-bind-child result
--
-- The first absent producer is earlier than those fields.  The checked raw
-- endpoint is Raw.global-beta-function-type and its exact term derivation is
-- Raw.global-value-ready-body-relation.  Their families are indexed by the
-- constructor-form two-Ctx world, whereas child-endpoint and child-relation
-- above are indexed by an existing CTX.World and CTI2 relation.  There is no
-- structural correspondence theorem between those indices.  Without it one
-- cannot state, let alone prove, the exact StructuralTermProvenance demanded by
-- the supplied child-target.  The completed frame witnesses
-- Raw.transport-frame-relation and Raw.mapped-alpha-reveal-relation therefore
-- remain relation-side evidence; they do not authorize fabricating W₁.
