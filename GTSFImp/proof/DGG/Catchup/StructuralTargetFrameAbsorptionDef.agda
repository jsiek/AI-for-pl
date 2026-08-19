module proof.DGG.Catchup.StructuralTargetFrameAbsorptionDef where

-- File Charter:
--   * Defines the target-frame absorption chain for structural value
--     instantiation spines.
--   * Records the non-recursive premises needed by target cast, reveal, and
--     conceal absorption rules in CastTermImprecision2.
--   * Provides checked root and strict-child constructor cells used by the
--     generalized structural worker.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Maybe using (Maybe)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty; TyVar; ＇_; `∀; ⇑ᵗ; _[_]ᵗ)
open import Consistency using (Env∼; extᵐ; _⊢_∼_; _[_]ᶜ)
open import Conversion using (Conv↑; Conv↓; replaceTy; 〖_,_↑_〗)
open import CastTerms using (Term; Value; _⟨_⟩; _↑_; _↓_)
open import Reduction using (keep; bind; applyTy; applyBody; _—→[_]_)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
import proof.DGG.Catchup.StructuralGeneratedFrameGeometryDef as GFG


data TargetFrameAbsorptionChain {Δᴸ Δᴿ Δ}
    (W : CTX.World Δᴸ Δᴿ Δ) (γ : CTX.CtxImp W)
    (A : Ty Δᴸ) :
    ∀ {B E : Ty Δᴿ}
    → InstantiationSpine B E
    → A CTX.⊑ᵂ⟨ W ⟩ E
    → Set₁ where

  tfa-[] : ∀ {B} {q : A CTX.⊑ᵂ⟨ W ⟩ B}
    → TargetFrameAbsorptionChain W γ A []ⁱ q

  tfa-type : ∀ {B C E}
      {eq : B ≡ C} {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A
        (type-transport-frame eq ▻ⁱ spine) q

  tfa-name : ∀ {B C E X}
      {D : Ty (suc Δᴿ)} {eqB : B ≡ `∀ D}
      {eqC : C ≡ D [ ＇ X ]ᵗ}
      {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A
        (name-type-app-frame D X eqB eqC ▻ⁱ spine) q

  tfa-cast : ∀ {B C E μ}
      {c : μ ⊢ B ∼ C} {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
    → A CTX.⊑ᵂ⟨ W ⟩ C
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A (cast-frame c ▻ⁱ spine) q

  tfa-reveal : ∀ {B C E Xᴿ?}
      {c : Conv↑ Δᴿ B C} {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
      {Wᵖ : CTX.World Δᴸ Δᴿ Δ}
      {γᵖ : CTX.CtxImp Wᵖ}
    → CTX.ImpEnvMono W Wᵖ
    → CTX.RebaseAtᴿ W Wᵖ Xᴿ?
    → CTX.SameCtx γ γᵖ
    → CTX.targetStoreʷ W Conv.⊢↑[ Xᴿ? ] c
    → (∀ {M N} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
        → W CTX.∣ γ ⊢² M ⊑ N ∶ p
        → Σ[ pᵖ ∈ A CTX.⊑ᵂ⟨ Wᵖ ⟩ B ]
            Wᵖ CTX.∣ γᵖ ⊢² M ⊑ N ∶ pᵖ)
    → (qC : A CTX.⊑ᵂ⟨ W ⟩ C)
    → (∀ {M N N₁}
        → W CTX.∣ γ ⊢² M ⊑ N ↑ c ∶ qC
        → (N ↑ c) —→[ keep ] N₁
        → Value N₁
        → W CTX.∣ γ ⊢² M ⊑ N₁ ∶ qC)
    → TargetFrameAbsorptionChain W γ A (mapInstantiationSpine keep spine) q
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A (reveal-frame c ▻ⁱ spine) q

  tfa-conceal : ∀ {B C E Xᴿ?}
      {c : Conv↓ Δᴿ B C} {spine : InstantiationSpine C E}
      {q : A CTX.⊑ᵂ⟨ W ⟩ E}
      {Wᵖ : CTX.World Δᴸ Δᴿ Δ}
      {γᵖ : CTX.CtxImp Wᵖ}
    → CTX.ImpEnvMono W Wᵖ
    → CTX.RebaseAtᴿ Wᵖ W Xᴿ?
    → CTX.SameCtx γ γᵖ
    → CTX.targetStoreʷ W Conv.⊢↓[ Xᴿ? ] c
    → (∀ {M N} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
        → W CTX.∣ γ ⊢² M ⊑ N ∶ p
        → Σ[ pᵖ ∈ A CTX.⊑ᵂ⟨ Wᵖ ⟩ B ]
            Wᵖ CTX.∣ γᵖ ⊢² M ⊑ N ∶ pᵖ)
    → (qC : A CTX.⊑ᵂ⟨ W ⟩ C)
    → (∀ {M N N₁}
        → W CTX.∣ γ ⊢² M ⊑ N ↓ c ∶ qC
        → (N ↓ c) —→[ keep ] N₁
        → Value N₁
        → W CTX.∣ γ ⊢² M ⊑ N₁ ∶ qC)
    → TargetFrameAbsorptionChain W γ A (mapInstantiationSpine keep spine) q
    → TargetFrameAbsorptionChain W γ A spine q
    → TargetFrameAbsorptionChain W γ A (conceal-frame c ▻ⁱ spine) q


target-frame-cast-absorption : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B C E : Ty Δᴿ} {μ : Env∼ Δᴿ}
    {c : μ ⊢ B ∼ C} {spine : InstantiationSpine C E}
    {p : A CTX.⊑ᵂ⟨ W ⟩ B}
    {q : A CTX.⊑ᵂ⟨ W ⟩ E}
  → TargetFrameAbsorptionChain W γ A (cast-frame c ▻ⁱ spine) q
  → W CTX.∣ γ ⊢² M ⊑ V ∶ p
  → Σ[ qC ∈ A CTX.⊑ᵂ⟨ W ⟩ C ]
      W CTX.∣ γ ⊢² M ⊑ V ⟨ c ⟩ ∶ qC
target-frame-cast-absorption (tfa-cast qC tail) rel =
  qC , CTI2.⊑cast² _ rel qC


target-frame-reveal-absorption : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B C E : Ty Δᴿ}
    {c : Conv↑ Δᴿ B C} {spine : InstantiationSpine C E}
    {p : A CTX.⊑ᵂ⟨ W ⟩ B}
    {q : A CTX.⊑ᵂ⟨ W ⟩ E}
  → TargetFrameAbsorptionChain W γ A (reveal-frame c ▻ⁱ spine) q
  → W CTX.∣ γ ⊢² M ⊑ V ∶ p
  → Σ[ qC ∈ A CTX.⊑ᵂ⟨ W ⟩ C ]
      W CTX.∣ γ ⊢² M ⊑ (V ↑ c) ∶ qC
target-frame-reveal-absorption
    (tfa-reveal mono rb sc c⊢ transport qC keep-rel keep-chain tail) rel
    with transport rel
target-frame-reveal-absorption
    (tfa-reveal mono rb sc c⊢ transport qC keep-rel keep-chain tail) rel
    | pᵖ , relᵖ =
  qC , CTI2.⊑reveal² mono rb sc c⊢ relᵖ qC


target-frame-conceal-absorption : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B C E : Ty Δᴿ}
    {c : Conv↓ Δᴿ B C} {spine : InstantiationSpine C E}
    {p : A CTX.⊑ᵂ⟨ W ⟩ B}
    {q : A CTX.⊑ᵂ⟨ W ⟩ E}
  → TargetFrameAbsorptionChain W γ A (conceal-frame c ▻ⁱ spine) q
  → W CTX.∣ γ ⊢² M ⊑ V ∶ p
  → Σ[ qC ∈ A CTX.⊑ᵂ⟨ W ⟩ C ]
      W CTX.∣ γ ⊢² M ⊑ (V ↓ c) ∶ qC
target-frame-conceal-absorption
    (tfa-conceal mono rb sc c⊢ transport qC keep-rel keep-chain tail) rel
    with transport rel
target-frame-conceal-absorption
    (tfa-conceal mono rb sc c⊢ transport qC keep-rel keep-chain tail) rel
    | pᵖ , relᵖ =
  qC , CTI2.⊑conceal² mono rb sc c⊢ relᵖ qC


allv-∀-child-frame-chain : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ Δᴿ Δ} {γ : CTX.CtxImp W}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {μ : Env∼ Δᴿ}
    {d : extᵐ μ ⊢ B ∼ C}
    {spine : InstantiationSpine (C [ ＇ X ]ᵗ) E}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ E}
  → GFG.StructuralAllGeneratedFrameGeometry W Aₛ C X
  → TargetFrameAbsorptionChain W γ Aₛ
      (mapInstantiationSpine keep spine) q
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame B X refl refl ▻ⁱ
        cast-frame (d [ ＇ X ]ᶜ) ▻ⁱ
        mapInstantiationSpine keep spine) q
allv-∀-child-frame-chain geom tail =
  tfa-name (tfa-cast
    (GFG.StructuralAllGeneratedFrameGeometry.qCast geom) tail)


allv-reveal-child-frame-chain : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ (suc Δᴿ) Δ} {γ : CTX.CtxImp W}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {c : Conv↑ (suc Δᴿ) C B}
    {spine : InstantiationSpine (B [ ＇ X ]ᵗ) E}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ applyTy (bind (＇ X)) E}
  → GFG.StructuralRevealGeneratedFrameGeometry W γ Aₛ B C X c
  → TargetFrameAbsorptionChain W γ Aₛ
      (mapInstantiationSpine (bind (＇ X)) spine) q
  → TargetFrameAbsorptionChain W γ Aₛ
      (mapInstantiationSpine keep
        (reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
          type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
          mapInstantiationSpine (bind (＇ X)) spine)) q
  → TargetFrameAbsorptionChain W γ Aₛ
      (mapInstantiationSpine keep
        (type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
          mapInstantiationSpine (bind (＇ X)) spine)) q
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame (applyBody (bind (＇ X)) C)
          Fin.zero refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        reveal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine) q
allv-reveal-child-frame-chain geom tail keep₁ keep₂ =
  tfa-name (tfa-type
    (tfa-reveal
      (RG.mono₁ geom) (RG.rebase₁ geom) (RG.same₁ geom)
      (RG.targetConversion₁ geom) (RG.transport₁ geom) (RG.q₁ geom)
      (RG.keep₁ geom) keep₁
      (tfa-reveal
        (RG.mono₂ geom) (RG.rebase₂ geom) (RG.same₂ geom)
        (RG.targetConversion₂ geom) (RG.transport₂ geom) (RG.q₂ geom)
        (RG.keep₂ geom) keep₂
        (tfa-type tail))))
  where
  module RG = GFG.StructuralRevealGeneratedFrameGeometry


allv-conceal-child-frame-chain : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ (suc Δᴿ) Δ} {γ : CTX.CtxImp W}
    {Aₛ : Ty Δᴸ} {B C : Ty (suc Δᴿ)} {E : Ty Δᴿ}
    {X : TyVar Δᴿ} {c : Conv↓ (suc Δᴿ) C B}
    {spine : InstantiationSpine (B [ ＇ X ]ᵗ) E}
    {q : Aₛ CTX.⊑ᵂ⟨ W ⟩ applyTy (bind (＇ X)) E}
  → GFG.StructuralConcealGeneratedFrameGeometry W γ Aₛ B C X c
  → TargetFrameAbsorptionChain W γ Aₛ
      (mapInstantiationSpine (bind (＇ X)) spine) q
  → TargetFrameAbsorptionChain W γ Aₛ
      (mapInstantiationSpine keep
        (reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
          type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
          mapInstantiationSpine (bind (＇ X)) spine)) q
  → TargetFrameAbsorptionChain W γ Aₛ
      (mapInstantiationSpine keep
        (type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
          mapInstantiationSpine (bind (＇ X)) spine)) q
  → TargetFrameAbsorptionChain W γ Aₛ
      (name-type-app-frame (applyBody (bind (＇ X)) C)
          Fin.zero refl refl ▻ⁱ
        type-transport-frame (applyBody-open-zero C) ▻ⁱ
        conceal-frame c ▻ⁱ
        reveal-frame (〖 Fin.zero , ⇑ᵗ (＇ X) ↑ B 〗) ▻ⁱ
        type-transport-frame (replace-zero-open B (＇ X)) ▻ⁱ
        mapInstantiationSpine (bind (＇ X)) spine) q
allv-conceal-child-frame-chain geom tail keep₁ keep₂ =
  tfa-name (tfa-type
    (tfa-conceal
      (CG.mono₁ geom) (CG.rebase₁ geom) (CG.same₁ geom)
      (CG.targetConversion₁ geom) (CG.transport₁ geom) (CG.q₁ geom)
      (CG.keep₁ geom) keep₁
      (tfa-reveal
        (CG.mono₂ geom) (CG.rebase₂ geom) (CG.same₂ geom)
        (CG.targetConversion₂ geom) (CG.transport₂ geom) (CG.q₂ geom)
        (CG.keep₂ geom) keep₂
        (tfa-type tail))))
  where
  module CG = GFG.StructuralConcealGeneratedFrameGeometry


root-value-instantiation-frame-chain : ∀ {Δᴸ Δᴿ Δ}
    {W : CTX.World Δᴸ (suc Δᴿ) Δ} {γ : CTX.CtxImp W}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {R : Ty Δᴿ}
    {q : A CTX.⊑ᵂ⟨ W ⟩
      applyBody (bind R) B [ ＇ Fin.zero ]ᵗ}
  → TargetFrameAbsorptionChain W γ A
      (name-type-app-frame (applyBody (bind R) B)
        Fin.zero refl refl ▻ⁱ []ⁱ) q
root-value-instantiation-frame-chain = tfa-name tfa-[]
