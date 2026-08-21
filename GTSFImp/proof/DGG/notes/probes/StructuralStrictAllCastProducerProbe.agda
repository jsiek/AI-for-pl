{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.StructuralStrictAllCastProducerProbe where

-- File Charter:
--   * Checks assembly of the strict universal-cast child after an exact
--     relation/frame producer has supplied the evidence absent from the live
--     strict-view surface.
--   * Separates the child relation and its target-indexed provenance from the
--     generated cast endpoint, cast classification, and keep-mapped tail
--     chain.
--   * Exhibits the fuel-zero obstruction for a concrete non-inert opened
--     identity cast.  This module changes no live proof surface.

open import Data.Empty using (⊥)
open import Data.Nat using (suc; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Base; Ty; TyVar; ＇_; ‵_; `∀; _[_]ᵗ)
open import Consistency using
  (Env∼; extᵐ; id; _⊢_∼_; ∀ᶜ_; _[_]ᶜ)
open import CastTerms using (Term; Value; _⟨_⟩)
open import Reduction using (keep)
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision as CTI2
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Catchup.StructuralTargetFrameAbsorptionDef
open import proof.DGG.Catchup.StructuralSpineTypingDef
open import proof.DGG.Catchup.StructuralTermProvenanceDef
open import proof.DGG.Catchup.StructuralStrictViewSurfaceDef
import proof.DGG.Catchup.StructuralGeneratedFrameGeometryDef as GFG


all-cast-child-assembly : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {μ : Env∼ Δᴿ}
    {d : extᵐ μ ⊢ B ∼ C}
    {p : Aₛ CTX.⊑ᵂ⟨ W ⟩ `∀ C}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ E}
  → (plan : StructuralNamePostPlan W Aₛ E q)
  → StructuralNameChainPlan {fuel = fuel} W γ Aₛ E q plan
  → W CTI2.∣ γ ⊢² M ⊑ V ⟨ ∀ᶜ d ⟩ ∶ p
  → Value M
  → Value V
  → (spine : InstantiationSpine (C [ ＇ X ]ᵗ) E)
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame C X refl refl ▻ⁱ spine) q
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame C X refl refl ▻ⁱ spine)
  → (child-target : StructuralTargetInstantiationPackage W V
      (name-type-app-frame B X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine))
  → (child-endpoint : Aₛ CTX.⊑ᵂ⟨ W ⟩ `∀ B)
  → (child-relation : W CTI2.∣ γ ⊢² M ⊑ V ∶ child-endpoint)
  → StructuralTermProvenance
      (StructuralTargetInstantiationPackage.structural-ext child-target)
      child-relation
  → (geometry : GFG.StructuralAllGeneratedFrameGeometry W Aₛ C X)
  → CastFrameClass {fuel = fuel} (d [ ＇ X ]ᶜ)
  → TargetFrameAbsorptionChain W γ Aₛ
      (mapInstantiationSpine keep spine) q
  → StructuralStrictChild {fuel = fuel} W γ M V Aₛ (`∀ B) E
      (name-type-app-frame B X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine)
      q child-target
all-cast-child-assembly {d = d} plan chain-plan rel vM vV spine
    (tfa-name parent-tail) (st-name typed-tail) child-target
    child-endpoint child-relation child-provenance geometry opened-class
    mapped-tail =
  record
    { child-endpoint = child-endpoint
    ; child-value = vV
    ; child-plan = plan
    ; child-chain-plan = chain-plan
    ; child-relation = child-relation
    ; child-provenance = child-provenance
    ; child-chain =
        allv-∀-child-frame-chain {d = d} geometry mapped-tail
    ; child-typed =
        st-name
          (st-cast opened-class (spine-typed-map-keep typed-tail))
    }


base-id-opened : ∀ {Δ} {μ : Env∼ Δ} {X : TyVar Δ} {ι : Base}
  → ((id { μ = extᵐ μ } (‵ ι)) [ ＇ X ]ᶜ) ≡ id { μ = μ } (‵ ι)
base-id-opened = refl


base-id-frame-class-zero-impossible : ∀ {Δ} {μ : Env∼ Δ} {ι : Base}
  → CastFrameClass {fuel = zero} (id { μ = μ } (‵ ι))
  → ⊥
base-id-frame-class-zero-impossible (cast-inert ())
base-id-frame-class-zero-impossible (cast-safe safe () provenance)
base-id-frame-class-zero-impossible (cast-residual () provenance)


base-id-all-child-typed-zero-impossible : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {μ : Env∼ Δᴿ} {X : TyVar Δᴿ} {ι : Base}
    {E : Ty Δᴿ} {spine : InstantiationSpine (‵ ι) E}
  → SpineTypedʷ {fuel = zero} W
      (name-type-app-frame (‵ ι) X refl refl ▻ⁱ
        cast-frame ((id { μ = extᵐ μ } (‵ ι)) [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine)
  → ⊥
base-id-all-child-typed-zero-impossible
    (st-name (st-cast opened-class typed-tail)) =
  base-id-frame-class-zero-impossible opened-class
